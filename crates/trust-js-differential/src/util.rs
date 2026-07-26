// Shared utilities for the TrustJS Channel-A harness: UTC date/time without
// foreign deps (proleptic Gregorian civil-from-days), strict YYYY-MM-DD
// validation, engine identity probing, git read-only queries, and the raw-lane
// stderr error-name scan.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

/// One named fail-closed finding. Any finding => the producing subcommand
/// exits 1.
#[derive(Debug, Clone)]
pub struct Finding {
    pub code: String,
    pub detail: String,
}

impl Finding {
    pub fn new(code: &str, detail: impl Into<String>) -> Self {
        Self { code: code.to_string(), detail: detail.into() }
    }

    pub fn render(&self) -> String {
        format!("[{}] {}", self.code, self.detail)
    }
}

/// Civil date from days since 1970-01-01 (Howard Hinnant's algorithm).
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}

fn unix_now_secs() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

/// Today's UTC date as `YYYY-MM-DD`.
pub fn today_utc() -> String {
    let secs = unix_now_secs();
    let (y, m, d) = civil_from_days((secs / 86_400) as i64);
    format!("{y:04}-{m:02}-{d:02}")
}

/// Current UTC instant as `YYYY-MM-DDTHH:MM:SSZ`.
pub fn now_utc_iso() -> String {
    let secs = unix_now_secs();
    let (y, m, d) = civil_from_days((secs / 86_400) as i64);
    let rem = secs % 86_400;
    format!("{y:04}-{m:02}-{d:02}T{:02}:{:02}:{:02}Z", rem / 3600, (rem % 3600) / 60, rem % 60)
}

fn is_leap(y: i64) -> bool {
    (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
}

/// Strict `YYYY-MM-DD` well-formedness including real calendar day bounds.
pub fn is_valid_date(s: &str) -> bool {
    let b = s.as_bytes();
    if b.len() != 10 || b[4] != b'-' || b[7] != b'-' {
        return false;
    }
    for (i, c) in b.iter().enumerate() {
        if i == 4 || i == 7 {
            continue;
        }
        if !c.is_ascii_digit() {
            return false;
        }
    }
    let y: i64 = s[0..4].parse().unwrap_or(0);
    let m: u32 = s[5..7].parse().unwrap_or(0);
    let d: u32 = s[8..10].parse().unwrap_or(0);
    if !(1..=12).contains(&m) {
        return false;
    }
    let dim = match m {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if is_leap(y) {
                29
            } else {
                28
            }
        }
        _ => unreachable!(),
    };
    (1..=dim).contains(&d)
}

/// The ledger validation date: `TRUST_JS262_VALIDATION_DATE` if set and
/// nonblank, else today (UTC). Zero-padded ISO dates compare lexicographically.
pub fn validation_date() -> String {
    match std::env::var("TRUST_JS262_VALIDATION_DATE") {
        Ok(v) if !v.trim().is_empty() => v.trim().to_string(),
        _ => today_utc(),
    }
}

/// `git -C <dir> rev-parse HEAD`, read-only. None on any failure.
pub fn git_head(dir: &Path) -> Option<String> {
    let out = Command::new("git").arg("-C").arg(dir).args(["rev-parse", "HEAD"]).output().ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if s.is_empty() { None } else { Some(s) }
}

/// Streaming SHA-256 of a file, lowercase hex.
pub fn sha256_file(path: &Path) -> std::io::Result<String> {
    use sha2::{Digest, Sha256};
    use std::io::Read;
    let mut f = std::fs::File::open(path)?;
    let mut hasher = Sha256::new();
    let mut buf = [0u8; 1 << 16];
    loop {
        let n = f.read(&mut buf)?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    let digest = hasher.finalize();
    let mut out = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        let _ = write!(out, "{byte:02x}");
    }
    Ok(out)
}

/// The external JavaScript engines the Channel-A differential runs against.
///
/// The version pin is part of the evidence, not a convenience: a trace
/// differential only says something about the exact engine builds the
/// divergence ledgers were classified against. A different Node changes trace
/// text and error-name spelling, which silently reclassifies excepted
/// divergences as new ones (or the reverse), so every resolution route asserts
/// the pin and a mismatch aborts the run instead of producing a scorecard whose
/// numbers no ledger describes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Engine {
    Node,
    Bun,
}

impl Engine {
    /// The program name looked up on `PATH`.
    pub const fn program(self) -> &'static str {
        match self {
            Engine::Node => "node",
            Engine::Bun => "bun",
        }
    }

    /// The override env var for an engine installed outside `PATH`.
    pub const fn env_key(self) -> &'static str {
        match self {
            Engine::Node => "TRUST_JS_NODE",
            Engine::Bun => "TRUST_JS_BUN",
        }
    }

    /// The CLI flag that overrides both `PATH` and the env var.
    pub const fn flag(self) -> &'static str {
        match self {
            Engine::Node => "--node",
            Engine::Bun => "--bun",
        }
    }

    /// The pinned version, normalized (no leading `v`).
    pub const fn pinned_version(self) -> &'static str {
        match self {
            Engine::Node => "24.5.0",
            Engine::Bun => "1.3.14",
        }
    }
}

/// Engine binary identity recorded into every scorecard/evidence artifact.
#[derive(Debug, Clone)]
pub struct ProbedEngine {
    pub path: PathBuf,
    pub version: String,
    pub sha256: String,
}

/// First executable file named `program` along a `PATH`-shaped search list.
fn which_on_path(path_var: Option<&OsStr>, program: &str) -> Option<PathBuf> {
    std::env::split_paths(path_var?)
        .filter(|dir| !dir.as_os_str().is_empty())
        .map(|dir| dir.join(program))
        .find(|cand| is_executable_file(cand))
}

#[cfg(unix)]
fn is_executable_file(path: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt;
    std::fs::metadata(path)
        .map(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
        .unwrap_or(false)
}

#[cfg(not(unix))]
fn is_executable_file(path: &Path) -> bool {
    path.is_file()
}

/// Resolve an engine binary: explicit flag, else the override env var, else
/// `PATH`. Every route is version-asserted by [`probe_engine`], so the override
/// buys a non-`PATH` install location, never an unpinned engine.
pub fn resolve_engine(engine: Engine, flag: Option<&str>) -> Result<PathBuf, String> {
    resolve_engine_with(
        engine,
        flag,
        std::env::var(engine.env_key()).ok().as_deref(),
        std::env::var_os("PATH").as_deref(),
    )
}

/// [`resolve_engine`] with the override and search list supplied, so the
/// precedence order is testable without mutating process-global environment.
fn resolve_engine_with(
    engine: Engine,
    flag: Option<&str>,
    env_value: Option<&str>,
    path_var: Option<&OsStr>,
) -> Result<PathBuf, String> {
    if let Some(f) = flag {
        let f = f.trim();
        if !f.is_empty() {
            return Ok(PathBuf::from(f));
        }
    }
    if let Some(v) = env_value {
        let v = v.trim();
        if !v.is_empty() {
            return Ok(PathBuf::from(v));
        }
    }
    which_on_path(path_var, engine.program()).ok_or_else(|| {
        format!(
            "no `{prog}` on PATH — install {prog} {pin}, or point {env} (or {flag}) at it",
            prog = engine.program(),
            pin = engine.pinned_version(),
            env = engine.env_key(),
            flag = engine.flag(),
        )
    })
}

/// The reported version, normalized for comparison against the pin: first
/// non-blank line, first whitespace-delimited token, leading `v` stripped.
/// Node prints `v24.5.0`, Bun prints `1.3.14`.
fn normalize_version(raw: &str) -> String {
    raw.lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .and_then(|l| l.split_whitespace().next())
        .unwrap_or("")
        .trim_start_matches('v')
        .to_string()
}

/// Probe an engine binary: `--version` output + binary sha256, with the version
/// pin asserted. Fail-closed: an unprobeable or off-pin engine is an error,
/// never a silent blank.
pub fn probe_engine(engine: Engine, path: &Path) -> anyhow::Result<ProbedEngine> {
    let out = Command::new(path)
        .arg("--version")
        .env("TZ", "UTC")
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .output()
        .map_err(|e| anyhow::anyhow!("cannot spawn engine {}: {e}", path.display()))?;
    if !out.status.success() {
        anyhow::bail!("engine {} --version exited nonzero", path.display());
    }
    let version = String::from_utf8_lossy(&out.stdout).trim().to_string();
    let normalized = normalize_version(&version);
    if normalized != engine.pinned_version() {
        anyhow::bail!(
            "{prog} at {path} reports {reported:?} (normalized {normalized:?}), pin is {pin} — \
             a differential result against an unpinned engine is not evidence",
            prog = engine.program(),
            path = path.display(),
            reported = version,
            pin = engine.pinned_version(),
        );
    }
    let sha256 = sha256_file(path)
        .map_err(|e| anyhow::anyhow!("cannot hash engine {}: {e}", path.display()))?;
    Ok(ProbedEngine { path: path.to_path_buf(), version, sha256 })
}


/// Does `haystack` contain `needle` as a byte subslice?
pub fn contains_subslice(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() || haystack.len() < needle.len() {
        return false;
    }
    haystack.windows(needle.len()).any(|w| w == needle)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn civil_dates() {
        assert_eq!(civil_from_days(0), (1970, 1, 1));
        assert_eq!(civil_from_days(19_723), (2024, 1, 1));
    }

    #[test]
    fn date_validation() {
        assert!(is_valid_date("2026-07-21"));
        assert!(is_valid_date("2024-02-29")); // leap
        assert!(!is_valid_date("2023-02-29"));
        assert!(!is_valid_date("2026-13-01"));
        assert!(!is_valid_date("2026-00-10"));
        assert!(!is_valid_date("2026-7-21"));
        assert!(!is_valid_date("2026/07/21"));
        assert!(!is_valid_date("2026-04-31"));
    }


    #[test]
    fn subslice() {
        assert!(contains_subslice(b"abc $262.detachArrayBuffer", b"$262."));
        assert!(!contains_subslice(b"abc $262", b"$262."));
    }

    #[test]
    fn version_normalization() {
        assert_eq!(normalize_version("v24.5.0"), "24.5.0"); // node
        assert_eq!(normalize_version("1.3.14"), "1.3.14"); // bun
        assert_eq!(normalize_version("\n  v24.5.0 \n"), "24.5.0");
        assert_eq!(normalize_version("1.3.14 (abcd)"), "1.3.14");
        assert_eq!(normalize_version(""), "");
    }

    #[test]
    fn engine_precedence_is_flag_then_env_then_path() {
        let got = resolve_engine_with(Engine::Node, Some("/flag/node"), Some("/env/node"), None)
            .expect("flag resolves");
        assert_eq!(got, PathBuf::from("/flag/node"));
        let got = resolve_engine_with(Engine::Node, None, Some("/env/node"), None)
            .expect("env resolves");
        assert_eq!(got, PathBuf::from("/env/node"));
        // A blank override is not an override.
        let got = resolve_engine_with(Engine::Bun, Some("  "), Some("/env/bun"), None)
            .expect("blank flag falls through to env");
        assert_eq!(got, PathBuf::from("/env/bun"));

        let dir = tempfile::tempdir().expect("tempdir");
        let on_path = dir.path().join("bun");
        std::fs::write(&on_path, "#!/bin/sh\n").expect("write stub");
        make_executable(&on_path);
        let got = resolve_engine_with(Engine::Bun, None, None, Some(dir.path().as_os_str()))
            .expect("PATH resolves");
        assert_eq!(got, on_path);
    }

    /// A missing engine is a named error naming the override, never a silent
    /// fallback to some other machine's install path.
    #[test]
    fn absent_engine_fails_closed() {
        let dir = tempfile::tempdir().expect("tempdir");
        let err = resolve_engine_with(Engine::Bun, None, None, Some(dir.path().as_os_str()))
            .expect_err("an empty search directory cannot resolve bun");
        assert!(err.contains("TRUST_JS_BUN"), "{err}");
        assert!(err.contains("1.3.14"), "{err}");
    }

    fn make_executable(path: &Path) {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755))
                .expect("chmod stub");
        }
        #[cfg(not(unix))]
        let _ = path;
    }

    /// The version pin is asserted on every route, including an explicit
    /// override path.
    #[test]
    fn off_pin_engine_is_rejected() {
        let dir = tempfile::tempdir().expect("tempdir");
        let fake = dir.path().join("node");
        std::fs::write(&fake, "#!/bin/sh\necho v22.0.0\n").expect("write stub");
        make_executable(&fake);
        let err = probe_engine(Engine::Node, &fake).expect_err("off-pin engine must fail closed");
        let msg = err.to_string();
        assert!(msg.contains("24.5.0"), "{msg}");
        assert!(msg.contains("not evidence"), "{msg}");
    }
}
