//! targo command execution for validation.
//!
//! Runs `targo check` and `targo test` with timeouts for fail-closed
//! validation. This rejects ambient host/upstream cargo for Trust-owned
//! validation.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::ffi::{OsStr, OsString};
use std::io::{self, Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::Duration;

use tempfile::TempDir;

const MAX_CAPTURED_OUTPUT_BYTES: usize = 1024 * 1024;
const TRUNCATED_OUTPUT_MARKER: &str = "[output truncated]\n";
const VALIDATION_ENV_DENYLIST: &[&str] = &[
    "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTFLAGS",
    "CARGO_BUILD_TARGET",
    "CARGO_BUILD_TARGET_DIR",
    "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_TARGET_DIR",
    "MAGIC_EXTRA_RUSTFLAGS",
    "RUSTC_WORKSPACE_WRAPPER",
    "RUSTC_WRAPPER",
    "RUSTFLAGS",
    "RUSTFLAGS_BOOTSTRAP",
    "RUSTFLAGS_NOT_BOOTSTRAP",
];

/// Result of running `cargo check` on a crate.
#[derive(Debug)]
pub(crate) struct CargoCheckResult {
    /// Whether the check passed (exit code 0, no errors).
    pub(crate) success: bool,
    /// Human-readable summary.
    pub(crate) summary: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TrustCargoCommand {
    pub(crate) program: PathBuf,
    pub(crate) prefix_args: Vec<OsString>,
}

#[derive(Debug)]
pub(crate) struct TrustCargoSearch {
    pub(crate) trust_targo_bin: Option<OsString>,
    pub(crate) path: Option<OsString>,
    pub(crate) repo_root: PathBuf,
}

impl TrustCargoSearch {
    fn from_env() -> Self {
        Self {
            trust_targo_bin: std::env::var_os("TRUST_TARGO_BIN"),
            path: std::env::var_os("PATH"),
            repo_root: trust_repo_root(),
        }
    }
}

/// Resolve the targo command used for validation.
///
/// Precedence is `TRUST_TARGO_BIN`, then `targo` on `PATH`, then local
/// standalone Trust toolchain paths (`build/*/stage2`). Host/upstream `cargo`
/// is intentionally not accepted because rewrite validation is Trust release
/// evidence.
pub(crate) fn resolve_targo(search: &TrustCargoSearch) -> Result<TrustCargoCommand, String> {
    if let Some(configured) = &search.trust_targo_bin {
        if configured.is_empty() {
            return Err("TRUST_TARGO_BIN is empty".to_string());
        }
        let path = PathBuf::from(configured);
        validate_targo_path(&path, "TRUST_TARGO_BIN")?;
        return Ok(TrustCargoCommand { program: path, prefix_args: Vec::new() });
    }

    if let Some(targo) = which_in_path(OsStr::new("targo"), search.path.as_deref()) {
        return Ok(TrustCargoCommand { program: targo, prefix_args: Vec::new() });
    }

    if let Some(stage2) = find_repo_stage2_targo(&search.repo_root) {
        return Ok(TrustCargoCommand { program: stage2, prefix_args: Vec::new() });
    }

    Err("Trust targo was not found; set TRUST_TARGO_BIN, put standalone targo on PATH, or use build/<host>/stage2/bin/targo; ambient host/upstream cargo is rejected".to_string())
}

/// Build a targo command for a validation subcommand.
pub(crate) fn build_targo_command(
    targo: &TrustCargoCommand,
    subcommand: &str,
    crate_path: &Path,
    target_dir: &Path,
) -> Command {
    let mut command = Command::new(&targo.program);
    command
        .args(&targo.prefix_args)
        .arg("--unverified")
        .arg(subcommand)
        .arg("--manifest-path")
        .arg(crate_path.join("Cargo.toml"))
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    sanitize_validation_env(&mut command);
    command.env("CARGO_SKIP_CACHE", "1").env("CARGO_TARGET_DIR", target_dir);
    command
}

fn sanitize_validation_env(command: &mut Command) {
    for name in VALIDATION_ENV_DENYLIST {
        command.env_remove(name);
    }
    for (name, _) in std::env::vars_os() {
        if is_validation_env_denied(&name) {
            command.env_remove(name);
        }
    }
}

pub(crate) fn is_validation_env_denied(name: &OsStr) -> bool {
    if VALIDATION_ENV_DENYLIST.iter().any(|denied| name == OsStr::new(denied)) {
        return true;
    }

    let Some(name) = name.to_str() else {
        return false;
    };
    name.starts_with("CARGO_TARGET_")
        && (name.ends_with("_LINKER")
            || name.ends_with("_RUNNER")
            || name.ends_with("_RUSTDOCFLAGS")
            || name.ends_with("_RUSTFLAGS"))
}

/// Run `targo check` on a crate directory with a timeout.
///
/// Returns `Ok(CargoCheckResult)` with the check outcome, or `Err(String)`
/// if the command cannot be spawned or times out.
pub(crate) fn run_cargo_check(
    crate_path: &Path,
    timeout: Duration,
) -> Result<CargoCheckResult, String> {
    if !crate_path.join("Cargo.toml").exists() {
        return Err(format!("No Cargo.toml found at {}", crate_path.display()));
    }

    // Trust: Use CARGO_SKIP_CACHE=1 and a per-invocation target dir to avoid
    // hitting the cargo wrapper's serialization lock during validation.
    let target_dir = temp_target_dir("trust-backprop-check-")?;
    let targo = resolve_targo(&TrustCargoSearch::from_env())?;
    let output = run_command_with_timeout(
        build_targo_command(&targo, "check", crate_path, target_dir.path()),
        "targo check",
        timeout,
    )?;

    let success = output.success;
    let summary = if success {
        "no errors".to_string()
    } else {
        // Extract error lines from stderr.
        let error_lines: Vec<&str> = output
            .stderr
            .lines()
            .filter(|l| l.contains("error[") || l.contains("error:"))
            .take(3)
            .collect();
        if error_lines.is_empty() {
            "compilation failed (no error details)".to_string()
        } else {
            error_lines.join("; ")
        }
    };

    Ok(CargoCheckResult { success, summary })
}

/// Result of running `cargo test` on a crate.
#[derive(Debug)]
pub(crate) struct CargoTestResult {
    /// Whether all tests passed (exit code 0).
    pub(crate) success: bool,
    /// Human-readable summary of the test run.
    pub(crate) summary: String,
}

/// Run `targo test` on a crate directory with a timeout.
///
/// Returns `Ok(CargoTestResult)` with the test outcome, or `Err(String)`
/// if the command cannot be spawned or times out.
pub(crate) fn run_cargo_test(
    crate_path: &Path,
    timeout: Duration,
) -> Result<CargoTestResult, String> {
    if !crate_path.join("Cargo.toml").exists() {
        return Err(format!("No Cargo.toml found at {}", crate_path.display()));
    }

    // Trust: Use CARGO_SKIP_CACHE=1 and a per-invocation target dir to avoid
    // hitting the cargo wrapper's serialization lock during validation.
    let target_dir = temp_target_dir("trust-backprop-test-")?;
    let targo = resolve_targo(&TrustCargoSearch::from_env())?;
    let output = run_command_with_timeout(
        build_targo_command(&targo, "test", crate_path, target_dir.path()),
        "targo test",
        timeout,
    )?;

    let success = output.success;
    let summary = extract_test_summary(&output.stdout, &output.stderr, success);

    Ok(CargoTestResult { success, summary })
}

/// Extract a human-readable summary from targo test output.
pub(crate) fn extract_test_summary(stdout: &str, stderr: &str, success: bool) -> String {
    // Look for the "test result:" line in stdout.
    for line in stdout.lines().chain(stderr.lines()) {
        let trimmed = line.trim();
        if trimmed.starts_with("test result:") {
            return trimmed.to_string();
        }
    }
    if success {
        "all tests passed".to_string()
    } else {
        let error_lines: Vec<&str> = stderr
            .lines()
            .filter(|l| l.contains("error[") || l.contains("error:"))
            .take(3)
            .collect();
        if error_lines.is_empty() {
            "tests failed (no summary found in output)".to_string()
        } else {
            format!("compilation/test error: {}", error_lines.join("; "))
        }
    }
}

fn validate_targo_path(path: &Path, source: &str) -> Result<(), String> {
    if path.file_name().and_then(OsStr::to_str) != Some("targo") {
        return Err(format!("{source} must point to a targo binary: {}", path.display()));
    }
    if !path.is_file() {
        return Err(format!("{source} is not executable: {}", path.display()));
    }
    Ok(())
}

fn which_in_path(name: &OsStr, path: Option<&OsStr>) -> Option<PathBuf> {
    for dir in std::env::split_paths(path?) {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn find_repo_stage2_targo(root: &Path) -> Option<PathBuf> {
    let direct = root.join("build/host/stage2/bin/targo");
    if direct.is_file() {
        return Some(direct);
    }
    let entries = std::fs::read_dir(root.join("build")).ok()?;
    for entry in entries.flatten() {
        let candidate = entry.path().join("stage2/bin/targo");
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn temp_target_dir(prefix: &str) -> Result<TempDir, String> {
    let dir = tempfile::Builder::new()
        .prefix(prefix)
        .tempdir()
        .map_err(|e| format!("Failed to create temporary target dir: {e}"))?;
    harden_temp_dir_permissions(&dir)
        .map_err(|e| format!("Failed to harden temporary target dir permissions: {e}"))?;
    Ok(dir)
}

#[cfg(unix)]
fn harden_temp_dir_permissions(dir: &TempDir) -> io::Result<()> {
    use std::os::unix::fs::PermissionsExt;

    std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o700))
}

#[cfg(not(unix))]
fn harden_temp_dir_permissions(_dir: &TempDir) -> io::Result<()> {
    Ok(())
}

#[derive(Debug)]
pub(crate) struct CommandOutput {
    pub(crate) success: bool,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

pub(crate) fn run_command_with_timeout(
    mut command: Command,
    command_name: &str,
    timeout: Duration,
) -> Result<CommandOutput, String> {
    let output_dir = temp_target_dir("trust-backprop-output-")?;
    let stdout_path = output_dir.path().join("stdout");
    let stderr_path = output_dir.path().join("stderr");
    let stdout = std::fs::File::create(&stdout_path)
        .map_err(|e| format!("Failed to capture stdout: {e}"))?;
    let stderr = std::fs::File::create(&stderr_path)
        .map_err(|e| format!("Failed to capture stderr: {e}"))?;

    command.stdin(Stdio::null()).stdout(Stdio::from(stdout)).stderr(Stdio::from(stderr));
    // Own process group: `cargo` spawns `rustc`, and a timeout that reaches
    // only the direct child leaves those compiles running against the same
    // target directory the next attempt is about to use.
    let mut child = trust_os::spawn_in_own_process_group(&mut command)
        .map_err(|e| format!("Failed to spawn {command_name}: {e}"))?;

    let start = std::time::Instant::now();
    let timeout_display = format_timeout_duration(timeout);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                return command_output(status, &stdout_path, &stderr_path);
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    match child.try_wait() {
                        Ok(Some(status)) => {
                            return command_output(status, &stdout_path, &stderr_path);
                        }
                        Ok(None) => {}
                        Err(e) => {
                            return Err(format!(
                                "Failed to recheck {command_name} status before timeout cleanup: {e}"
                            ));
                        }
                    }

                    if let Err(kill_error) = trust_os::kill_process_group(&mut child) {
                        return match child.try_wait() {
                            Ok(Some(status)) => command_output(status, &stdout_path, &stderr_path),
                            Ok(None) => Err(format!(
                                "{command_name} timed out after {timeout_display} (fail-closed); failed to kill timed-out child: {kill_error}"
                            )),
                            Err(wait_error) => Err(format!(
                                "{command_name} timed out after {timeout_display} (fail-closed); failed to kill timed-out child: {kill_error}; failed to recheck status: {wait_error}"
                            )),
                        };
                    }

                    if let Err(wait_error) = child.wait() {
                        return Err(format!(
                            "{command_name} timed out after {timeout_display} (fail-closed); failed to wait after kill: {wait_error}"
                        ));
                    }
                    return Err(format!(
                        "{command_name} timed out after {timeout_display} (fail-closed)"
                    ));
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                let kill_result = child.kill();
                let wait_result = child.wait();
                return match (kill_result, wait_result) {
                    (Ok(()), Ok(_)) => Err(format!("Failed to check {command_name} status: {e}")),
                    (Err(kill_error), Ok(_)) => Err(format!(
                        "Failed to check {command_name} status: {e}; failed to kill child during cleanup: {kill_error}"
                    )),
                    (Ok(()), Err(wait_error)) => Err(format!(
                        "Failed to check {command_name} status: {e}; failed to wait during cleanup: {wait_error}"
                    )),
                    (Err(kill_error), Err(wait_error)) => Err(format!(
                        "Failed to check {command_name} status: {e}; failed to kill child during cleanup: {kill_error}; failed to wait during cleanup: {wait_error}"
                    )),
                };
            }
        }
    }
}

fn format_timeout_duration(timeout: Duration) -> String {
    format!("{timeout:?}")
}

fn command_output(
    status: ExitStatus,
    stdout_path: &Path,
    stderr_path: &Path,
) -> Result<CommandOutput, String> {
    Ok(CommandOutput {
        success: status.success(),
        stdout: read_bounded_output(stdout_path)
            .map_err(|e| format!("Failed to read captured stdout: {e}"))?,
        stderr: read_bounded_output(stderr_path)
            .map_err(|e| format!("Failed to read captured stderr: {e}"))?,
    })
}

fn read_bounded_output(path: &Path) -> io::Result<String> {
    let mut file = std::fs::File::open(path)?;
    let len = file.metadata()?.len();
    let truncated = len > MAX_CAPTURED_OUTPUT_BYTES as u64;
    if truncated {
        file.seek(SeekFrom::End(-(MAX_CAPTURED_OUTPUT_BYTES as i64)))?;
    }

    let mut captured = BoundedOutput::new(MAX_CAPTURED_OUTPUT_BYTES);
    let mut chunk = [0; 8192];
    loop {
        match file.read(&mut chunk) {
            Ok(0) => break,
            Ok(n) => captured.push(&chunk[..n]),
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    let mut was_truncated = truncated || captured.truncated;
    let mut output = captured.into_string_lossy();
    if output.len() > MAX_CAPTURED_OUTPUT_BYTES {
        output = trim_string_front_to_byte_len(output, MAX_CAPTURED_OUTPUT_BYTES);
        was_truncated = true;
    }
    if was_truncated {
        output.insert_str(0, TRUNCATED_OUTPUT_MARKER);
    }
    Ok(output)
}

fn trim_string_front_to_byte_len(input: String, max_len: usize) -> String {
    if input.len() <= max_len {
        return input;
    }

    let mut start = input.len() - max_len;
    while !input.is_char_boundary(start) {
        start += 1;
    }
    input[start..].to_string()
}

struct BoundedOutput {
    bytes: Vec<u8>,
    start: usize,
    len: usize,
    truncated: bool,
}

impl BoundedOutput {
    fn new(capacity: usize) -> Self {
        Self { bytes: vec![0; capacity], start: 0, len: 0, truncated: false }
    }

    fn push(&mut self, mut chunk: &[u8]) {
        let capacity = self.bytes.len();
        if capacity == 0 || chunk.is_empty() {
            return;
        }

        if chunk.len() >= capacity {
            self.bytes.copy_from_slice(&chunk[chunk.len() - capacity..]);
            self.start = 0;
            self.len = capacity;
            self.truncated = true;
            return;
        }

        if self.len < capacity {
            let available = capacity - self.len;
            let to_append = available.min(chunk.len());
            let write_at = (self.start + self.len) % capacity;
            self.copy_at(write_at, &chunk[..to_append]);
            self.len += to_append;
            chunk = &chunk[to_append..];
        }

        if !chunk.is_empty() {
            self.truncated = true;
            self.copy_at(self.start, chunk);
            self.start = (self.start + chunk.len()) % capacity;
        }
    }

    fn copy_at(&mut self, offset: usize, chunk: &[u8]) {
        let capacity = self.bytes.len();
        let first = (capacity - offset).min(chunk.len());
        self.bytes[offset..offset + first].copy_from_slice(&chunk[..first]);
        if first < chunk.len() {
            self.bytes[..chunk.len() - first].copy_from_slice(&chunk[first..]);
        }
    }

    fn into_string_lossy(self) -> String {
        let mut output = Vec::with_capacity(self.len);
        if self.len > 0 {
            let first = (self.bytes.len() - self.start).min(self.len);
            output.extend_from_slice(&self.bytes[self.start..self.start + first]);
            if first < self.len {
                output.extend_from_slice(&self.bytes[..self.len - first]);
            }
        }

        String::from_utf8_lossy(&output).into_owned()
    }
}

fn trust_repo_root() -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest_dir.parent().and_then(Path::parent).unwrap_or(manifest_dir).to_path_buf()
}
