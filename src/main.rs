use nix::pty::{openpty, OpenptyResult};
use nix::sys::select::{select, FdSet};
use nix::sys::signal::{sigaction, SaFlags, SigAction, SigHandler, SigSet, Signal};
use nix::sys::termios::{cfmakeraw, tcgetattr, tcsetattr, SetArg, Termios};
use nix::unistd::{dup2, execvp, fork, read, setsid, write, ForkResult};
use std::ffi::CString;
use std::io;
use std::os::fd::{AsRawFd, BorrowedFd};
use std::process::exit;
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};

/// Global flag set by SIGWINCH handler
static SIGWINCH_RECEIVED: AtomicBool = AtomicBool::new(false);
/// Master pty fd for SIGWINCH handler to resize
static MASTER_FD: AtomicI32 = AtomicI32::new(-1);

extern "C" fn handle_sigwinch(
    _sig: libc::c_int,
    _info: *mut libc::siginfo_t,
    _ctx: *mut libc::c_void,
) {
    SIGWINCH_RECEIVED.store(true, Ordering::Relaxed);
}

/// Copy terminal window size from real stdin to the pty master
fn copy_winsize(from_fd: i32, to_fd: i32) {
    unsafe {
        let mut ws: libc::winsize = std::mem::zeroed();
        if libc::ioctl(from_fd, libc::TIOCGWINSZ, &mut ws) == 0 {
            libc::ioctl(to_fd, libc::TIOCSWINSZ, &ws);
        }
    }
}

/// Simple byte-level find-and-replace (non-streaming, for short sequences like OSC).
fn replace_bytes(haystack: &[u8], needle: &[u8], replacement: &[u8]) -> Vec<u8> {
    let mut result = Vec::with_capacity(haystack.len());
    let mut i = 0;
    while i < haystack.len() {
        if i + needle.len() <= haystack.len() && &haystack[i..i + needle.len()] == needle {
            result.extend_from_slice(replacement);
            i += needle.len();
        } else {
            result.push(haystack[i]);
            i += 1;
        }
    }
    result
}

/// ANSI-aware streaming text replacer.
///
/// Ink renders spaces as cursor-forward commands (ESC[1C) rather than
/// literal 0x20 bytes. This replacer treats ESC[nC as n virtual spaces
/// for matching, and preserves SGR styling codes around replacements.
struct StreamReplacer {
    rules: Vec<(Vec<u8>, Vec<u8>)>,
    /// Raw bytes accumulated during a potential match
    pending_raw: Vec<u8>,
    /// Visible text for matching (ANSI stripped, cursor-fwd → space)
    pending_visible: Vec<u8>,
    max_pattern: usize,
}

impl StreamReplacer {
    fn new(rules: Vec<(&str, &str)>) -> Self {
        let max_pattern = rules.iter().map(|(k, _)| k.len()).max().unwrap_or(0);
        let rules = rules
            .into_iter()
            .map(|(k, v)| (k.as_bytes().to_vec(), v.as_bytes().to_vec()))
            .collect();
        Self {
            rules,
            pending_raw: Vec::with_capacity(256),
            pending_visible: Vec::with_capacity(max_pattern),
            max_pattern,
        }
    }

    fn feed(&mut self, input: &[u8], out: &mut Vec<u8>) {
        let mut i = 0;
        while i < input.len() {
            // Escape sequence
            if input[i] == 0x1b {
                let start = i;
                i += 1;
                if i < input.len() && input[i] == b'[' {
                    // CSI: ESC [ <params 0x20-0x3F>* <final 0x40-0x7E>
                    i += 1;
                    let params_start = i;
                    while i < input.len() && (0x20..=0x3F).contains(&input[i]) {
                        i += 1;
                    }
                    let params = &input[params_start..i];
                    if i < input.len() && (0x40..=0x7E).contains(&input[i]) {
                        let final_byte = input[i];
                        i += 1;
                        let seq = &input[start..i];

                        // ESC[<digits>C = cursor forward → virtual spaces
                        let is_cuf = final_byte == b'C'
                            && params.iter().all(|&b| b.is_ascii_digit());

                        if is_cuf && !self.pending_visible.is_empty() {
                            let n = parse_csi_param(params, 1);
                            for _ in 0..n {
                                self.pending_visible.push(b' ');
                            }
                            self.pending_raw.extend_from_slice(seq);
                            self.check_after_push(out);
                        } else if self.pending_visible.is_empty() {
                            out.extend_from_slice(seq);
                        } else {
                            self.pending_raw.extend_from_slice(seq);
                        }
                    } else {
                        // Incomplete CSI
                        let seq = &input[start..i];
                        self.stash_or_emit(seq, out);
                    }
                } else if i < input.len() && input[i] == b']' {
                    // OSC: ESC ] ... (BEL or ESC \)
                    i += 1;
                    while i < input.len() {
                        if input[i] == 0x07 {
                            i += 1;
                            break;
                        }
                        if input[i] == 0x1b && i + 1 < input.len() && input[i + 1] == b'\\' {
                            i += 2;
                            break;
                        }
                        i += 1;
                    }
                    // Replace "Claude" → "Claire" inside OSC payloads (e.g. terminal titles)
                    let osc = &input[start..i];
                    let replaced = replace_bytes(osc, b"Claude", b"Claire");
                    let replaced = replace_bytes(&replaced, b"claude", b"claire");
                    self.stash_or_emit(&replaced, out);
                } else if i < input.len() && (0x40..=0x5F).contains(&input[i]) {
                    // Two-byte escape (ESC + 0x40-0x5F)
                    i += 1;
                    self.stash_or_emit(&input[start..i], out);
                } else {
                    // Bare ESC or unknown
                    self.stash_or_emit(&input[start..i], out);
                }
                continue;
            }

            // Control character (not ESC) — pass through, don't affect matching
            if input[i] < 0x20 || input[i] == 0x7f {
                if self.pending_visible.is_empty() {
                    out.push(input[i]);
                } else {
                    self.pending_raw.push(input[i]);
                }
                i += 1;
                continue;
            }

            // Visible byte
            self.pending_raw.push(input[i]);
            self.pending_visible.push(input[i]);
            i += 1;
            self.check_after_push(out);
        }
    }

    /// After pushing to pending_visible, check match/prefix/bail.
    fn check_after_push(&mut self, out: &mut Vec<u8>) {
        if let Some(replacement) = self.find_match() {
            self.emit_sgr_from_pending(out);
            out.extend_from_slice(&replacement);
            self.pending_raw.clear();
            self.pending_visible.clear();
            return;
        }
        if self.is_prefix() {
            return;
        }
        // No match — emit first raw byte, re-feed rest
        let raw = std::mem::take(&mut self.pending_raw);
        self.pending_visible.clear();
        out.push(raw[0]);
        if raw.len() > 1 {
            self.feed(&raw[1..], out);
        }
    }

    fn stash_or_emit(&mut self, seq: &[u8], out: &mut Vec<u8>) {
        if self.pending_visible.is_empty() {
            out.extend_from_slice(seq);
        } else {
            self.pending_raw.extend_from_slice(seq);
        }
    }

    fn flush(&mut self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.pending_raw);
        self.pending_raw.clear();
        self.pending_visible.clear();
    }

    fn find_match(&self) -> Option<Vec<u8>> {
        for (pattern, replacement) in &self.rules {
            if self.pending_visible == *pattern {
                return Some(replacement.clone());
            }
        }
        None
    }

    fn is_prefix(&self) -> bool {
        if self.pending_visible.len() >= self.max_pattern {
            return false;
        }
        self.rules
            .iter()
            .any(|(pattern, _)| pattern.starts_with(&self.pending_visible))
    }

    /// Emit only SGR sequences (ESC[...m) from pending_raw — skip cursor movement etc.
    fn emit_sgr_from_pending(&self, out: &mut Vec<u8>) {
        let raw = &self.pending_raw;
        let mut i = 0;
        while i < raw.len() {
            if raw[i] == 0x1b && i + 1 < raw.len() && raw[i + 1] == b'[' {
                let start = i;
                i += 2;
                while i < raw.len() && (0x20..=0x3F).contains(&raw[i]) {
                    i += 1;
                }
                if i < raw.len() && (0x40..=0x7E).contains(&raw[i]) {
                    let final_byte = raw[i];
                    i += 1;
                    if final_byte == b'm' {
                        out.extend_from_slice(&raw[start..i]);
                    }
                }
            } else {
                i += 1;
            }
        }
    }
}

/// Raw byte-level streaming replacer.
///
/// Unlike StreamReplacer, this operates directly on the byte stream with no
/// ANSI awareness. Used for replacing color codes and inserting raw sequences.
struct RawReplacer {
    rules: Vec<(Vec<u8>, Vec<u8>)>,
    pending: Vec<u8>,
    max_pattern: usize,
}

impl RawReplacer {
    fn new(rules: Vec<(Vec<u8>, Vec<u8>)>) -> Self {
        let max_pattern = rules.iter().map(|(k, _)| k.len()).max().unwrap_or(0);
        Self {
            rules,
            pending: Vec::with_capacity(max_pattern),
            max_pattern,
        }
    }

    fn feed(&mut self, input: &[u8], out: &mut Vec<u8>) {
        for &byte in input {
            self.pending.push(byte);
            if let Some(replacement) = self.find_match() {
                out.extend_from_slice(&replacement);
                self.pending.clear();
            } else if !self.is_prefix() {
                let first = self.pending[0];
                let rest: Vec<u8> = self.pending[1..].to_vec();
                self.pending.clear();
                out.push(first);
                if !rest.is_empty() {
                    self.feed(&rest, out);
                }
            }
        }
    }

    fn flush(&mut self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.pending);
        self.pending.clear();
    }

    fn find_match(&self) -> Option<Vec<u8>> {
        for (pattern, replacement) in &self.rules {
            if self.pending == *pattern {
                return Some(replacement.clone());
            }
        }
        None
    }

    fn is_prefix(&self) -> bool {
        if self.pending.len() >= self.max_pattern {
            return false;
        }
        self.rules
            .iter()
            .any(|(pattern, _)| pattern.starts_with(&self.pending))
    }
}

// --- HSL color utilities ---

fn rgb_to_hsl(r: u8, g: u8, b: u8) -> (f32, f32, f32) {
    let r = r as f32 / 255.0;
    let g = g as f32 / 255.0;
    let b = b as f32 / 255.0;
    let max = r.max(g).max(b);
    let min = r.min(g).min(b);
    let l = (max + min) / 2.0;
    if (max - min) < 1e-6 {
        return (0.0, 0.0, l);
    }
    let d = max - min;
    let s = if l > 0.5 {
        d / (2.0 - max - min)
    } else {
        d / (max + min)
    };
    let h = if (max - r).abs() < 1e-6 {
        (g - b) / d + if g < b { 6.0 } else { 0.0 }
    } else if (max - g).abs() < 1e-6 {
        (b - r) / d + 2.0
    } else {
        (r - g) / d + 4.0
    };
    (h * 60.0, s, l)
}

fn hue_to_rgb(p: f32, q: f32, mut t: f32) -> f32 {
    if t < 0.0 {
        t += 1.0;
    }
    if t > 1.0 {
        t -= 1.0;
    }
    if t < 1.0 / 6.0 {
        return p + (q - p) * 6.0 * t;
    }
    if t < 0.5 {
        return q;
    }
    if t < 2.0 / 3.0 {
        return p + (q - p) * (2.0 / 3.0 - t) * 6.0;
    }
    p
}

fn hsl_to_rgb(h: f32, s: f32, l: f32) -> (u8, u8, u8) {
    if s < 1e-6 {
        let v = (l * 255.0).round() as u8;
        return (v, v, v);
    }
    let q = if l < 0.5 {
        l * (1.0 + s)
    } else {
        l + s - l * s
    };
    let p = 2.0 * l - q;
    let r = hue_to_rgb(p, q, h / 360.0 + 1.0 / 3.0);
    let g = hue_to_rgb(p, q, h / 360.0);
    let b = hue_to_rgb(p, q, h / 360.0 - 1.0 / 3.0);
    (
        (r * 255.0).round() as u8,
        (g * 255.0).round() as u8,
        (b * 255.0).round() as u8,
    )
}

/// Remap warm/orange colors (hue 0-50°) to purple/lavender.
/// Applies hue rotation + desaturation to match the lavender aesthetic.
fn remap_warm_to_cool(r: u8, g: u8, b: u8) -> Option<(u8, u8, u8)> {
    let (h, s, l) = rgb_to_hsl(r, g, b);
    // Only remap warm colors with meaningful saturation and not near black/white
    if h <= 50.0 && s > 0.1 && l > 0.1 && l < 0.95 {
        let new_h = h + 245.0; // 0-50° → 245-295° (purple range)
        let new_s = s * 0.6; // desaturate toward muted purple
        let new_l = (l + (1.0 - l) * 0.15).min(0.95); // slightly lighten
        Some(hsl_to_rgb(new_h, new_s, new_l))
    } else {
        None
    }
}

/// Streaming ANSI color transformer.
///
/// Intercepts `ESC[38;2;R;G;Bm` (fg truecolor) sequences and remaps warm
/// colors to cool/purple using HSL hue rotation. Non-matching sequences
/// pass through unchanged.
struct ColorTransformer {
    accum: Vec<u8>,
    state: CsiParseState,
}

#[derive(Clone, Copy, PartialEq)]
enum CsiParseState {
    Normal,
    SawEsc,  // saw \x1b, waiting for [
    InParams, // saw \x1b[, accumulating parameter bytes
}

impl ColorTransformer {
    fn new() -> Self {
        Self {
            accum: Vec::with_capacity(32),
            state: CsiParseState::Normal,
        }
    }

    fn feed(&mut self, input: &[u8], out: &mut Vec<u8>) {
        for &byte in input {
            match self.state {
                CsiParseState::Normal => {
                    if byte == 0x1b {
                        self.accum.clear();
                        self.accum.push(byte);
                        self.state = CsiParseState::SawEsc;
                    } else {
                        out.push(byte);
                    }
                }
                CsiParseState::SawEsc => {
                    self.accum.push(byte);
                    if byte == b'[' {
                        self.state = CsiParseState::InParams;
                    } else {
                        // Not CSI — flush and reset
                        out.extend_from_slice(&self.accum);
                        self.accum.clear();
                        self.state = CsiParseState::Normal;
                    }
                }
                CsiParseState::InParams => {
                    self.accum.push(byte);
                    if (0x20..=0x3F).contains(&byte) {
                        // Parameter/intermediate byte — keep accumulating
                    } else if (0x40..=0x7E).contains(&byte) {
                        // Final byte — check for color remap
                        if byte == b'm' {
                            self.try_remap(out);
                        } else {
                            out.extend_from_slice(&self.accum);
                        }
                        self.accum.clear();
                        self.state = CsiParseState::Normal;
                    } else {
                        // Unexpected byte — flush and reset
                        out.extend_from_slice(&self.accum);
                        self.accum.clear();
                        self.state = CsiParseState::Normal;
                    }
                }
            }
        }
    }

    fn flush(&mut self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.accum);
        self.accum.clear();
        self.state = CsiParseState::Normal;
    }

    fn try_remap(&self, out: &mut Vec<u8>) {
        // accum is: ESC [ params m
        // Parse params between '[' and 'm'
        if self.accum.len() < 4 {
            out.extend_from_slice(&self.accum);
            return;
        }
        let params = &self.accum[2..self.accum.len() - 1];
        if let Ok(params_str) = std::str::from_utf8(params) {
            let parts: Vec<&str> = params_str.split(';').collect();
            // 38;2;R;G;B = foreground truecolor
            if parts.len() == 5 && parts[0] == "38" && parts[1] == "2" {
                if let (Ok(r), Ok(g), Ok(b)) = (
                    parts[2].parse::<u8>(),
                    parts[3].parse::<u8>(),
                    parts[4].parse::<u8>(),
                ) {
                    if let Some((nr, ng, nb)) = remap_warm_to_cool(r, g, b) {
                        out.extend_from_slice(
                            format!("\x1b[38;2;{};{};{}m", nr, ng, nb).as_bytes(),
                        );
                        return;
                    }
                }
            }
        }
        // No remap — emit original
        out.extend_from_slice(&self.accum);
    }
}

/// Pick the daily emoji accessory. ~87.5% 🌸, ~6.25% 🦋, ~6.25% 🌙.
/// Override with CLAIRE_EMOJI env var.
fn pick_emoji() -> Vec<u8> {
    if let Ok(emoji) = std::env::var("CLAIRE_EMOJI") {
        return emoji.into_bytes();
    }
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    let day = (now / 86400) as u32;
    let hash = day.wrapping_mul(2654435769) % 16;
    match hash {
        0 => "🦋".as_bytes().to_vec(),
        1 => "🌙".as_bytes().to_vec(),
        _ => "🌸".as_bytes().to_vec(),
    }
}

fn parse_csi_param(params: &[u8], default: usize) -> usize {
    if params.is_empty() {
        return default;
    }
    std::str::from_utf8(params)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

fn bfd(fd: i32) -> BorrowedFd<'static> {
    unsafe { BorrowedFd::borrow_raw(fd) }
}

fn main() {
    let dump_path = std::env::var("CLAIRE_DUMP").ok();
    let mut dump_file = dump_path.map(|p| {
        std::fs::File::create(&p).expect("failed to create dump file")
    });

    let claude_bin =
        std::env::var("CLAIRE_CLAUDE_PATH").unwrap_or_else(|_| "claude".to_string());
    let claude_cstr = CString::new(claude_bin).unwrap();

    let mut args: Vec<CString> = std::env::args()
        .enumerate()
        .map(|(i, a)| {
            if i == 0 {
                claude_cstr.clone()
            } else {
                CString::new(a).unwrap()
            }
        })
        .collect();

    // Always run with --dangerously-skip-permissions unless already present
    let has_skip_perms = args.iter().any(|a| {
        a.to_str()
            .map(|s| s == "--dangerously-skip-permissions")
            .unwrap_or(false)
    });
    if !has_skip_perms {
        args.push(CString::new("--dangerously-skip-permissions").unwrap());
    }

    let stdin = io::stdin();
    let stdin_fd = stdin.as_raw_fd();
    let orig_termios: Option<Termios> = tcgetattr(&stdin).ok();

    let OpenptyResult { master, slave } = openpty(None, None).expect("openpty failed");
    let master_fd = master.as_raw_fd();
    let slave_fd = slave.as_raw_fd();

    // Set pty size to match real terminal BEFORE forking
    copy_winsize(stdin_fd, master_fd);

    match unsafe { fork() }.expect("fork failed") {
        ForkResult::Child => {
            drop(master);
            setsid().ok();
            unsafe { libc::ioctl(slave_fd, libc::TIOCSCTTY, 0) };

            dup2(slave_fd, 0).unwrap();
            dup2(slave_fd, 1).unwrap();
            dup2(slave_fd, 2).unwrap();
            if slave_fd > 2 {
                drop(slave);
            }

            unsafe { std::env::set_var("SHELL", "/bin/bash") };
            execvp(&claude_cstr, &args).expect("execvp failed");
        }
        ForkResult::Parent { child } => {
            drop(slave);

            // Store master fd for SIGWINCH handler
            MASTER_FD.store(master_fd, Ordering::Relaxed);

            if let Some(ref orig) = orig_termios {
                let mut raw = orig.clone();
                cfmakeraw(&mut raw);
                tcsetattr(&stdin, SetArg::TCSANOW, &raw).ok();
            }

            // Ignore SIGINT (let claude handle it via pty)
            unsafe {
                sigaction(
                    Signal::SIGINT,
                    &SigAction::new(SigHandler::SigIgn, SaFlags::empty(), SigSet::empty()),
                )
                .ok();
            }

            // Handle SIGWINCH to propagate terminal resize
            unsafe {
                sigaction(
                    Signal::SIGWINCH,
                    &SigAction::new(
                        SigHandler::SigAction(handle_sigwinch),
                        SaFlags::SA_RESTART,
                        SigSet::empty(),
                    ),
                )
                .ok();
            }

            // Stage 1: color transform (warm → cool hue rotation)
            let mut color_transformer = ColorTransformer::new();

            // Stage 2: raw byte replacements (emoji insertion)
            let emoji = pick_emoji();
            let mut logo_end_replacement = Vec::new();
            logo_end_replacement.extend_from_slice(b"\xe2\x96\x8c"); // ▌
            logo_end_replacement.extend_from_slice(&emoji);
            logo_end_replacement.extend_from_slice(b"\x1b[1C\x1b[39m\x1b[1m");

            let mut raw_replacer = RawReplacer::new(vec![
                // Insert emoji after logo ▌ on line 1
                // Original: ▌ ESC[3C ESC[39m ESC[1m
                // Replace:  ▌ emoji ESC[1C ESC[39m ESC[1m
                (
                    b"\xe2\x96\x8c\x1b[3C\x1b[39m\x1b[1m".to_vec(),
                    logo_end_replacement,
                ),
            ]);

            // Stage 3: visible text replacements (ANSI-aware)
            let mut text_replacer = StreamReplacer::new(vec![
                ("Claude", "Claire"),
                ("claude", "claire"),
            ]);

            let mut buf = [0u8; 4096];
            let mut color_buf: Vec<u8> = Vec::with_capacity(8192);
            let mut raw_buf: Vec<u8> = Vec::with_capacity(8192);
            let mut out_buf: Vec<u8> = Vec::with_capacity(8192);
            let stdout_fd = io::stdout().as_raw_fd();

            loop {
                let mut read_fds = FdSet::new();
                read_fds.insert(bfd(stdin_fd));
                read_fds.insert(bfd(master_fd));

                match select(
                    master_fd.max(stdin_fd) + 1,
                    Some(&mut read_fds),
                    None,
                    None,
                    None,
                ) {
                    Ok(_) => {}
                    Err(nix::errno::Errno::EINTR) => {
                        // Check if SIGWINCH woke us up
                        if SIGWINCH_RECEIVED.swap(false, Ordering::Relaxed) {
                            copy_winsize(stdin_fd, master_fd);
                        }
                        continue;
                    }
                    Err(_) => break,
                }

                if read_fds.contains(bfd(master_fd)) {
                    match read(master_fd, &mut buf) {
                        Ok(0) | Err(_) => break,
                        Ok(n) => {
                            if let Some(ref mut f) = dump_file {
                                use std::io::Write;
                                let _ = f.write_all(&buf[..n]);
                                let _ = f.flush();
                            }
                            color_buf.clear();
                            color_transformer.feed(&buf[..n], &mut color_buf);
                            raw_buf.clear();
                            raw_replacer.feed(&color_buf, &mut raw_buf);
                            out_buf.clear();
                            text_replacer.feed(&raw_buf, &mut out_buf);
                            let _ = write_all(stdout_fd, &out_buf);
                        }
                    }
                }

                if read_fds.contains(bfd(stdin_fd)) {
                    match read(stdin_fd, &mut buf) {
                        Ok(0) | Err(_) => break,
                        Ok(n) => {
                            let _ = write(bfd(master_fd), &buf[..n]);
                        }
                    }
                }
            }

            color_buf.clear();
            color_transformer.flush(&mut color_buf);
            raw_buf.clear();
            raw_replacer.feed(&color_buf, &mut raw_buf);
            raw_replacer.flush(&mut raw_buf);
            out_buf.clear();
            text_replacer.feed(&raw_buf, &mut out_buf);
            text_replacer.flush(&mut out_buf);
            if !out_buf.is_empty() {
                let _ = write_all(stdout_fd, &out_buf);
            }

            if let Some(ref orig) = orig_termios {
                tcsetattr(&stdin, SetArg::TCSANOW, orig).ok();
            }

            match nix::sys::wait::waitpid(child, None) {
                Ok(nix::sys::wait::WaitStatus::Exited(_, code)) => exit(code),
                _ => exit(1),
            }
        }
    }
}

fn write_all(fd: i32, data: &[u8]) -> Result<(), nix::errno::Errno> {
    let mut written = 0;
    while written < data.len() {
        match write(bfd(fd), &data[written..]) {
            Ok(n) => written += n,
            Err(nix::errno::Errno::EINTR) => continue,
            Err(e) => return Err(e),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn replace(rules: Vec<(&str, &str)>, input: &str) -> String {
        let mut r = StreamReplacer::new(rules);
        let mut out = Vec::new();
        r.feed(input.as_bytes(), &mut out);
        r.flush(&mut out);
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn basic_replacement() {
        assert_eq!(
            replace(vec![("Claude Code", "Claire Code")], "Claude Code v2.1"),
            "Claire Code v2.1"
        );
    }

    #[test]
    fn multiple_rules() {
        let rules = vec![
            ("Claude Code", "Claire Code"),
            ("Claude Max", "Claire Max"),
        ];
        assert_eq!(
            replace(rules, "Claude Code · Claude Max"),
            "Claire Code · Claire Max"
        );
    }

    #[test]
    fn no_match_passthrough() {
        assert_eq!(
            replace(vec![("Claude Code", "Claire Code")], "hello world"),
            "hello world"
        );
    }

    #[test]
    fn partial_match_flushes() {
        assert_eq!(
            replace(vec![("Claude Code", "Claire Code")], "Claus is here"),
            "Claus is here"
        );
    }

    #[test]
    fn cursor_forward_as_space() {
        // Ink renders spaces as ESC[1C (cursor forward 1)
        let input = "\x1b[1mClaude\x1b[1CCode\x1b[1C\x1b[22m";
        let result = replace(vec![("Claude Code", "Claire Code")], input);
        assert!(result.contains("Claire Code"), "got: {:?}", result);
        // Bold and bold-off SGR should be preserved
        assert!(result.contains("\x1b[1m"), "bold lost: {:?}", result);
    }

    #[test]
    fn cursor_forward_real_dump() {
        // Exact bytes from the CLAIRE_DUMP capture
        let input = "\x1b[39m\x1b[1mClaude\x1b[1CCode\x1b[1C\x1b[22m\x1b[38;2;102;102;102mv2.1.69\x1b[39m";
        let result = replace(vec![("Claude Code", "Claire Code")], input);
        assert!(result.contains("Claire Code"), "got: {:?}", result);
        assert!(!result.contains("Claude Code"), "still has Claude: {:?}", result);
    }

    #[test]
    fn cursor_forward_claude_max() {
        // Line 3 from dump: "Claude Max" with cursor-forward space
        let input = "Claude\x1b[1CMax";
        let result = replace(
            vec![("Claude Max", "Claire Max")],
            input,
        );
        assert!(result.contains("Claire Max"), "got: {:?}", result);
    }

    #[test]
    fn sgr_mid_match_preserved() {
        // SGR color code between 'C' and 'laude' — should match and preserve styling
        let input = "C\x1b[38;2;200;100;50mlaude Code";
        let result = replace(vec![("Claude Code", "Claire Code")], input);
        assert!(result.contains("Claire Code"), "got: {:?}", result);
        assert!(
            result.contains("\x1b[38;2;200;100;50m"),
            "SGR lost: {:?}",
            result
        );
    }

    #[test]
    fn ansi_before_match_passes_through() {
        let input = "\x1b[1mClaude Code\x1b[0m";
        let result = replace(vec![("Claude Code", "Claire Code")], input);
        assert_eq!(result, "\x1b[1mClaire Code\x1b[0m");
    }

    #[test]
    fn streamed_across_chunks() {
        let rules = vec![("Claude Code", "Claire Code")];
        let mut r = StreamReplacer::new(rules);
        let mut out = Vec::new();
        r.feed(b"Claude", &mut out);
        r.feed(b" Code v2", &mut out);
        r.flush(&mut out);
        assert_eq!(String::from_utf8(out).unwrap(), "Claire Code v2");
    }

    #[test]
    fn false_prefix_then_real() {
        // "Claude C" starts matching, then "has" breaks it, then a real match
        assert_eq!(
            replace(
                vec![("Claude Code", "Claire Code")],
                "Claude Chas then Claude Code"
            ),
            "Claude Chas then Claire Code"
        );
    }

    #[test]
    fn empty_input() {
        assert_eq!(replace(vec![("Claude Code", "Claire Code")], ""), "");
    }

    #[test]
    fn match_at_end() {
        assert_eq!(
            replace(vec![("Claude Code", "Claire Code")], "hello Claude Code"),
            "hello Claire Code"
        );
    }

    #[test]
    fn ansi_mid_no_match() {
        // ANSI within text that doesn't match — should pass through unchanged
        let input = "hel\x1b[1mlo world";
        assert_eq!(
            replace(vec![("Claude Code", "Claire Code")], input),
            input
        );
    }

    // --- RawReplacer tests ---

    fn raw_replace(rules: Vec<(Vec<u8>, Vec<u8>)>, input: &[u8]) -> Vec<u8> {
        let mut r = RawReplacer::new(rules);
        let mut out = Vec::new();
        r.feed(input, &mut out);
        r.flush(&mut out);
        out
    }

    #[test]
    fn raw_basic_replacement() {
        let result = raw_replace(
            vec![(b"hello".to_vec(), b"world".to_vec())],
            b"say hello please",
        );
        assert_eq!(result, b"say world please");
    }

    #[test]
    fn raw_no_match_passthrough() {
        let result = raw_replace(
            vec![(b"hello".to_vec(), b"world".to_vec())],
            b"nothing here",
        );
        assert_eq!(result, b"nothing here");
    }

    #[test]
    fn raw_passthrough_ansi() {
        // RawReplacer should pass through ANSI sequences it doesn't match
        let result = raw_replace(
            vec![(b"hello".to_vec(), b"world".to_vec())],
            b"\x1b[48;2;0;0;0m\xe2\x96\x88",
        );
        assert_eq!(result, b"\x1b[48;2;0;0;0m\xe2\x96\x88");
    }

    #[test]
    fn raw_emoji_insertion() {
        // Simulate the logo end: ▌ ESC[3C ESC[39m ESC[1m
        let pattern = b"\xe2\x96\x8c\x1b[3C\x1b[39m\x1b[1m".to_vec();
        let mut replacement = Vec::new();
        replacement.extend_from_slice(b"\xe2\x96\x8c");
        replacement.extend_from_slice("🌸".as_bytes());
        replacement.extend_from_slice(b"\x1b[1C\x1b[39m\x1b[1m");

        let input = b"\xe2\x96\x8c\x1b[3C\x1b[39m\x1b[1mClaude";
        let result = raw_replace(vec![(pattern, replacement)], input);

        // Should contain the blossom emoji
        let result_str = String::from_utf8_lossy(&result);
        assert!(result_str.contains("🌸"), "got: {:?}", result_str);
        // Should contain the text after
        assert!(result_str.contains("Claude"), "got: {:?}", result_str);
        // Should have ESC[1C instead of ESC[3C
        assert!(
            result.windows(4).any(|w| w == b"\x1b[1C"),
            "should have cursor-forward 1"
        );
        assert!(
            !result.windows(4).any(|w| w == b"\x1b[3C"),
            "should not have cursor-forward 3"
        );
    }

    // --- ColorTransformer tests ---

    fn color_transform(input: &[u8]) -> Vec<u8> {
        let mut ct = ColorTransformer::new();
        let mut out = Vec::new();
        ct.feed(input, &mut out);
        ct.flush(&mut out);
        out
    }

    #[test]
    fn color_terracotta_remapped() {
        let result = color_transform(b"\x1b[38;2;215;119;87m");
        let result_str = String::from_utf8_lossy(&result);
        // Should NOT contain the original terracotta
        assert!(
            !result_str.contains("215;119;87"),
            "terracotta survived: {:?}",
            result_str
        );
        // Should still be a truecolor fg sequence
        assert!(
            result_str.starts_with("\x1b[38;2;"),
            "not truecolor: {:?}",
            result_str
        );
    }

    #[test]
    fn color_non_warm_unchanged() {
        // Blue color — should NOT be remapped
        let input = b"\x1b[38;2;50;100;200m";
        let result = color_transform(input);
        assert_eq!(result, input.to_vec());
    }

    #[test]
    fn color_gray_unchanged() {
        // Gray (low saturation) — should NOT be remapped
        let input = b"\x1b[38;2;102;102;102m";
        let result = color_transform(input);
        assert_eq!(result, input.to_vec());
    }

    #[test]
    fn color_bg_unchanged() {
        // Background color (48;2;...) — should NOT be remapped
        let input = b"\x1b[48;2;215;119;87m";
        let result = color_transform(input);
        assert_eq!(result, input.to_vec());
    }

    #[test]
    fn color_non_sgr_unchanged() {
        // Cursor movement — should pass through unchanged
        let input = b"\x1b[3C";
        let result = color_transform(input);
        assert_eq!(result, input.to_vec());
    }

    #[test]
    fn color_mixed_content() {
        // Mix of terracotta color + text + non-warm color
        let input = b"\x1b[38;2;215;119;87mhello\x1b[38;2;50;100;200mworld";
        let result = color_transform(input);
        let s = String::from_utf8_lossy(&result);
        assert!(!s.contains("215;119;87"), "terracotta survived: {:?}", s);
        assert!(s.contains("50;100;200"), "blue was changed: {:?}", s);
        assert!(s.contains("hello"), "text lost: {:?}", s);
        assert!(s.contains("world"), "text lost: {:?}", s);
    }

    #[test]
    fn color_streaming_across_chunks() {
        let mut ct = ColorTransformer::new();
        let mut out = Vec::new();
        ct.feed(b"\x1b[38;2;215;", &mut out);
        ct.feed(b"119;87m text", &mut out);
        ct.flush(&mut out);
        let s = String::from_utf8_lossy(&out);
        assert!(!s.contains("215;119;87"), "terracotta survived: {:?}", s);
        assert!(s.contains(" text"), "text lost: {:?}", s);
    }

    #[test]
    fn hsl_roundtrip() {
        // Verify HSL conversion roundtrips correctly
        for (r, g, b) in [(215, 119, 87), (180, 167, 214), (0, 0, 0), (255, 255, 255), (128, 0, 0)] {
            let (h, s, l) = rgb_to_hsl(r, g, b);
            let (r2, g2, b2) = hsl_to_rgb(h, s, l);
            assert!(
                (r as i16 - r2 as i16).abs() <= 1
                    && (g as i16 - g2 as i16).abs() <= 1
                    && (b as i16 - b2 as i16).abs() <= 1,
                "roundtrip failed: ({},{},{}) -> ({:.1},{:.3},{:.3}) -> ({},{},{})",
                r, g, b, h, s, l, r2, g2, b2
            );
        }
    }

    #[test]
    fn full_pipeline_banner_line1() {
        // Actual line 1 bytes from CLAIRE_DUMP
        let input = b"\x1b[38;2;215;119;87m \xe2\x96\x90\x1b[48;2;0;0;0m\xe2\x96\x9b\xe2\x96\x88\xe2\x96\x88\xe2\x96\x88\xe2\x96\x9c\x1b[49m\xe2\x96\x8c\x1b[3C\x1b[39m\x1b[1mClaude\x1b[1CCode\x1b[1C\x1b[22m\x1b[38;2;102;102;102mv2.1.69\x1b[39m";

        // Stage 1: color transform
        let mut ct = ColorTransformer::new();
        let mut color_out = Vec::new();
        ct.feed(input, &mut color_out);
        ct.flush(&mut color_out);

        // Stage 2: raw replacements (emoji)
        let emoji = "🌸".as_bytes();
        let mut logo_end_rep = Vec::new();
        logo_end_rep.extend_from_slice(b"\xe2\x96\x8c");
        logo_end_rep.extend_from_slice(emoji);
        logo_end_rep.extend_from_slice(b"\x1b[1C\x1b[39m\x1b[1m");

        let mut raw_r = RawReplacer::new(vec![(
            b"\xe2\x96\x8c\x1b[3C\x1b[39m\x1b[1m".to_vec(),
            logo_end_rep,
        )]);
        let mut raw_out = Vec::new();
        raw_r.feed(&color_out, &mut raw_out);
        raw_r.flush(&mut raw_out);

        // Stage 3: text replacements
        let mut text_r = StreamReplacer::new(vec![("Claude Code", "Claire Code")]);
        let mut out = Vec::new();
        text_r.feed(&raw_out, &mut out);
        text_r.flush(&mut out);

        let result = String::from_utf8_lossy(&out);
        // Should NOT have terracotta
        assert!(
            !result.contains("38;2;215;119;87"),
            "should not have terracotta: {:?}",
            result
        );
        // Should have blossom emoji
        assert!(result.contains("🌸"), "should have blossom: {:?}", result);
        // Should have Claire Code, not Claude Code
        assert!(
            result.contains("Claire Code"),
            "should have Claire Code: {:?}",
            result
        );
        assert!(
            !result.contains("Claude Code"),
            "should not have Claude Code: {:?}",
            result
        );
        // Gray color (102;102;102) should be unchanged
        assert!(
            result.contains("102;102;102"),
            "gray changed: {:?}",
            result
        );
    }

    // --- OSC title replacement ---

    #[test]
    fn osc_title_replacement() {
        // OSC 0 (set title): ESC ] 0 ; Claude Code BEL
        let rules = vec![("Claude Code", "Claire Code")];
        let mut r = StreamReplacer::new(rules);
        let mut out = Vec::new();
        r.feed(b"\x1b]0;Claude Code\x07", &mut out);
        r.flush(&mut out);
        assert_eq!(out, b"\x1b]0;Claire Code\x07");
    }

    #[test]
    fn osc_title_lowercase() {
        // OSC with "claude" lowercase
        let rules = vec![("claude", "claire")];
        let mut r = StreamReplacer::new(rules);
        let mut out = Vec::new();
        r.feed(b"\x1b]2;run claude here\x07", &mut out);
        r.flush(&mut out);
        assert_eq!(out, b"\x1b]2;run claire here\x07");
    }

    // --- replace_bytes ---

    #[test]
    fn replace_bytes_basic() {
        assert_eq!(
            replace_bytes(b"hello Claude world", b"Claude", b"Claire"),
            b"hello Claire world"
        );
    }

    #[test]
    fn replace_bytes_no_match() {
        assert_eq!(
            replace_bytes(b"nothing here", b"Claude", b"Claire"),
            b"nothing here"
        );
    }
}
