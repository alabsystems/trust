// trust_wp CLI backend
//
// Phase 1 implementation: delegates to trust_wp CLI via subprocess.
// Will be replaced by direct in-process integration in Phase 2.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Subprocess-based trust_wp backend.
//!
//! Invokes the trust_wp deductive verifier as a subprocess, passing contracts
//! via stdin/files and parsing the structured result protocol from stderr.
//! This is the Phase 1 implementation; Phase 2 (trust-build feature) will
//! call trust-wp's verification context in-process via `TyCtxt`.

use std::io::Read;
use std::process::{Child, Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use crate::backend::TrustWpBackend;
use crate::config::{DiagConfig, TrustWpConfig};
use crate::contract::ContractSet;
use crate::error::TrustWpLibError;
use crate::result::{
    DiagLevel, DiagnosticMessage, FunctionVerdict, LoopInvariant, TrustWpResult, Verdict,
    VerificationCounts,
};

/// Wire line prefix for trust-wp's structured result protocol.
const WIRE_PREFIX: &str = "TRUST_WP_RESULT:v1";

#[cfg(unix)]
const SPAWN_EXECUTABLE_BUSY_RETRIES: usize = 20;
#[cfg(unix)]
const SPAWN_EXECUTABLE_BUSY_BACKOFF: Duration = Duration::from_millis(10);

struct SubprocessOutput {
    stdout: String,
    stderr: String,
    exit_code: i32,
    timed_out: bool,
}

#[cfg(unix)]
fn spawn_trust_wp_command(cmd: &mut Command) -> std::io::Result<Child> {
    let mut attempts = 0;
    loop {
        match trust_os::spawn_in_own_process_group(cmd) {
            Ok(child) => return Ok(child),
            Err(error)
                if error.kind() == std::io::ErrorKind::ExecutableFileBusy
                    && attempts < SPAWN_EXECUTABLE_BUSY_RETRIES =>
            {
                attempts += 1;
                thread::sleep(SPAWN_EXECUTABLE_BUSY_BACKOFF);
            }
            Err(error) => return Err(error),
        }
    }
}

#[cfg(not(unix))]
fn spawn_trust_wp_command(cmd: &mut Command) -> std::io::Result<Child> {
    trust_os::spawn_in_own_process_group(cmd)
}

/// Probe for the trust_wp binary.
///
/// Trust #soundness (H1, fail-closed hardening): ONLY an explicitly-configured
/// `TRUST_WP_PATH` env var is honored. There is deliberately NO `$PATH`
/// discovery (`which cargo-trust-wp` / `which trust-wp`): this backend is
/// embedded in the compiler's router, and the compiler path must never let an
/// arbitrary binary that happens to be on a developer's PATH become a proof
/// authority (the in-tree `trust-wp` placeholder binary prints usage and exits
/// 0 for ANY args — under PATH discovery it would have been engaged as a
/// verifier). Absent/invalid `TRUST_WP_PATH` ⇒ decline (`BinaryNotFound`,
/// which the router surfaces as `Unknown` — never a verdict).
fn probe_trust_wp_path() -> Option<String> {
    probe_trust_wp_path_from(std::env::var("TRUST_WP_PATH").ok())
}

/// Pure core of [`probe_trust_wp_path`] (unit-testable without mutating the
/// process environment). Accepts only an explicitly-configured, existing path.
fn probe_trust_wp_path_from(env_path: Option<String>) -> Option<String> {
    let path = env_path?;
    if !path.is_empty() && std::path::Path::new(&path).exists() { Some(path) } else { None }
}

/// Subprocess-based trust_wp backend.
///
/// Communicates with trust_wp via the CLI, parsing the structured result
/// protocol for machine-readable output. This is the Phase 1 implementation
/// that will be superseded by direct in-process integration when the
/// `trust-build` feature is enabled.
pub struct CliBackend {
    /// Resolved solver path.
    solver_path: Option<String>,
    /// Extra solver arguments.
    solver_args: Vec<String>,
    /// Timeout in milliseconds.
    timeout_ms: u64,
    /// Diagnostic configuration.
    diag_config: DiagConfig,
    /// Memory tracking level.
    track_level: String,
    /// Whether to use structured result protocol.
    structured_results: bool,
}

impl CliBackend {
    /// Create a new CLI backend from config.
    pub(crate) fn new(config: &TrustWpConfig) -> Self {
        Self::new_with_path_probe(config, probe_trust_wp_path)
    }

    fn new_with_path_probe(config: &TrustWpConfig, probe: impl FnOnce() -> Option<String>) -> Self {
        Self {
            // Capture ambient executable authority per backend/session. A
            // process-global cache made the first TRUST_WP_PATH value sticky
            // across later compiler invocations in long-lived hosts.
            solver_path: config.solver_path.clone().or_else(probe),
            solver_args: config.solver_args.clone(),
            timeout_ms: config.timeout_ms,
            diag_config: config.diagnostics.clone(),
            track_level: config.track_level.clone(),
            structured_results: config.structured_results,
        }
    }

    /// Resolve the solver path captured for this backend/session.
    fn resolve_path(&self) -> Result<&str, TrustWpLibError> {
        self.solver_path.as_deref().ok_or_else(|| TrustWpLibError::BinaryNotFound {
            reason: "set TRUST_WP_PATH to an explicit trust-wp binary (PATH discovery \
                         is deliberately disabled for this compiler-embedded lane)"
                .to_string(),
        })
    }

    /// Build the command arguments for a verification run.
    fn build_verify_args(&self, function_name: &str, contracts: &ContractSet) -> Vec<String> {
        let mut args = vec![
            "--function".to_string(),
            function_name.to_string(),
            "--track".to_string(),
            self.track_level.clone(),
        ];

        // Contract arguments
        for contract in &contracts.requires {
            args.push("--requires".to_string());
            args.push(contract.expression.clone());
        }
        for contract in &contracts.ensures {
            args.push("--ensures".to_string());
            args.push(contract.expression.clone());
        }
        for contract in &contracts.invariants {
            args.push("--invariant".to_string());
            args.push(contract.expression.clone());
        }

        if contracts.trusted {
            args.push("--trusted".to_string());
        }

        // Extra user args
        args.extend(self.solver_args.iter().cloned());

        args
    }

    /// Run trust_wp and capture stdout + stderr.
    fn run_subprocess(&self, args: &[String]) -> Result<SubprocessOutput, TrustWpLibError> {
        let path = self.resolve_path()?;

        let mut cmd = Command::new(path);
        cmd.args(args).stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());

        // Enable structured result protocol
        if self.structured_results {
            cmd.env("TRUST_WP_RESULT_PROTOCOL", "1");
        }

        let mut child = spawn_trust_wp_command(&mut cmd)?;
        let mut stdout = child.stdout.take().ok_or_else(|| TrustWpLibError::ConfigError {
            reason: "failed to capture trust_wp stdout".to_string(),
        })?;
        let mut stderr = child.stderr.take().ok_or_else(|| TrustWpLibError::ConfigError {
            reason: "failed to capture trust_wp stderr".to_string(),
        })?;

        let stdout_reader = thread::spawn(move || {
            let mut buf = Vec::new();
            stdout.read_to_end(&mut buf).map(|_| buf)
        });
        let stderr_reader = thread::spawn(move || {
            let mut buf = Vec::new();
            stderr.read_to_end(&mut buf).map(|_| buf)
        });

        let bounded = trust_os::wait_bounded(&mut child, Duration::from_millis(self.timeout_ms))?;
        let (status, timed_out) = (bounded.status, bounded.timed_out);

        let stdout = stdout_reader.join().map_err(|_| TrustWpLibError::ConfigError {
            reason: "trust-wp stdout reader thread panicked".to_string(),
        })??;
        let stderr = stderr_reader.join().map_err(|_| TrustWpLibError::ConfigError {
            reason: "trust-wp stderr reader thread panicked".to_string(),
        })??;

        let stdout = String::from_utf8_lossy(&stdout).to_string();
        let stderr = String::from_utf8_lossy(&stderr).to_string();
        let exit_code = status.code().unwrap_or(-1);

        Ok(SubprocessOutput { stdout, stderr, exit_code, timed_out })
    }

    /// Parse the structured result wire line from stderr.
    fn parse_wire_line(stderr: &str) -> Option<VerificationCounts> {
        for line in stderr.lines() {
            if let Some(rest) = line.strip_prefix(WIRE_PREFIX) {
                let rest = rest.trim();
                return Some(parse_counts(rest));
            }
        }
        None
    }

    /// Parse diagnostics from stderr, excluding the wire line.
    fn parse_diagnostics(stderr: &str) -> Vec<DiagnosticMessage> {
        stderr
            .lines()
            .filter(|line| !line.trim().is_empty() && !line.starts_with(WIRE_PREFIX))
            .map(|line| {
                let (level, message) = if line.contains("error") {
                    (DiagLevel::Error, line.to_string())
                } else if line.contains("warning") {
                    (DiagLevel::Warning, line.to_string())
                } else {
                    (DiagLevel::Note, line.to_string())
                };
                DiagnosticMessage { level, message, location: None }
            })
            .collect()
    }
}

impl TrustWpBackend for CliBackend {
    fn verify(
        &self,
        function_name: &str,
        contracts: &ContractSet,
    ) -> Result<TrustWpResult, TrustWpLibError> {
        let start = Instant::now();
        let args = self.build_verify_args(function_name, contracts);
        let output = self.run_subprocess(&args)?;
        let elapsed = start.elapsed().as_millis() as u64;

        // Check timeout
        if output.timed_out || elapsed >= self.timeout_ms {
            return Ok(TrustWpResult {
                verdict: Verdict::Timeout,
                function_verdicts: Vec::new(),
                loop_invariants: Vec::new(),
                proof_certificate: None,
                time_ms: elapsed,
                diagnostics: Vec::new(),
                function_name: function_name.to_string(),
                counts: VerificationCounts::default(),
            });
        }

        // Parse diagnostics
        let diagnostics = if self.diag_config == DiagConfig::Capture {
            Self::parse_diagnostics(&output.stderr)
        } else {
            Vec::new()
        };

        // Parse structured results. Trust #soundness (H1, fail-closed
        // hardening): the structured wire line is the ONLY machine-readable
        // verification evidence this backend has. If it is absent (placeholder
        // or stale binary, protocol drift, a wrapper swallowing stderr,
        // `structured_results` disabled), deriving a verdict from the exit code
        // alone would let ANY exit-0 binary mint a full deductive Proved — a
        // false-proof channel. Absent wire line ⇒ `Verdict::Unknown`, NEVER
        // default-zero counts.
        let Some(counts) = Self::parse_wire_line(&output.stderr) else {
            return Ok(TrustWpResult {
                verdict: Verdict::Unknown {
                    reason: format!(
                        "trust-wp produced no {WIRE_PREFIX} wire line (exit code {}); \
                         refusing to derive a verdict from the exit code alone (fail-closed)",
                        output.exit_code
                    ),
                },
                function_verdicts: Vec::new(),
                loop_invariants: Vec::new(),
                proof_certificate: None,
                time_ms: elapsed,
                diagnostics,
                function_name: function_name.to_string(),
                counts: VerificationCounts::default(),
            });
        };

        // Derive verdict from exit code and counts
        let verdict = derive_verdict(output.exit_code, &counts, &output.stdout);

        // Parse function-level verdicts from stdout
        let function_verdicts = parse_function_verdicts(&output.stdout, function_name);

        // Parse any inferred invariants from stdout
        let loop_invariants = parse_inferred_invariants(&output.stdout, function_name);

        Ok(TrustWpResult {
            verdict,
            function_verdicts,
            loop_invariants,
            proof_certificate: None,
            time_ms: elapsed,
            diagnostics,
            function_name: function_name.to_string(),
            counts,
        })
    }

    fn infer_invariants(&self, function_name: &str) -> Result<Vec<LoopInvariant>, TrustWpLibError> {
        let mut args = vec![
            "--function".to_string(),
            function_name.to_string(),
            "--infer-invariants".to_string(),
        ];
        args.extend(self.solver_args.iter().cloned());

        let output = self.run_subprocess(&args)?;

        if output.timed_out {
            return Err(TrustWpLibError::Timeout { timeout_ms: self.timeout_ms });
        }

        // Parse invariants from output
        let invariants = parse_inferred_invariants(&output.stdout, function_name);
        Ok(invariants)
    }
}

/// Derive the overall verdict from exit code and counts.
fn derive_verdict(exit_code: i32, counts: &VerificationCounts, _stdout: &str) -> Verdict {
    match exit_code {
        0 => {
            // Trust #soundness (round-17): exit code 0 is the producer's CLAIM of
            // "no soundness gap", but the bridge must INDEPENDENTLY enforce that
            // contract against the structured wire counters it already parsed.
            // A stale binary, a wrapper that swallows the nonzero exit code, or
            // protocol drift could surface exit 0 while the run actually ASSUMED
            // functions / relied on axiom dependencies / trusted / skipped them —
            // a conditional result. Trusting raw exit 0 alone would then mint a
            // full deductive Proved (AssuranceLevel::Sound) for a conditional
            // verification: a false-PROVE. Cross-check and fail closed to Unknown
            // on any reported gap (mirrors the native-ay and bare-unsat fail-closed
            // posture). On the happy path the producer already drives these to 0
            // (exit 2 on a gap), so this only fires on an exit/wire divergence and
            // can never false-FAIL a genuinely clean verification.
            let gap =
                counts.assumed + counts.verified_with_axiom_deps + counts.trusted + counts.skipped;
            if gap > 0 {
                Verdict::Unknown {
                    reason: format!(
                        "trust-wp reported exit 0 but structured counters indicate a soundness \
                         gap (assumed={}, axiom_deps={}, trusted={}, skipped={}); not proof-grade",
                        counts.assumed,
                        counts.verified_with_axiom_deps,
                        counts.trusted,
                        counts.skipped
                    ),
                }
            } else if counts.verified == 0 {
                // Trust #soundness (H1): an exit-0 run whose wire line reports
                // ZERO verified obligations carries no positive verification
                // evidence — e.g. a shim emitting a bare "TRUST_WP_RESULT:v1"
                // line parses to all-zero counts. Zero-evidence must never
                // become a full deductive Verified. Fail closed to Unknown.
                Verdict::Unknown {
                    reason: "trust-wp reported exit 0 but zero verified obligations on the \
                             wire line (no positive verification evidence); not proof-grade"
                        .to_string(),
                }
            } else {
                Verdict::Verified
            }
        }
        1 => Verdict::Failed,
        2 => {
            if counts.errors > 0 {
                Verdict::Error { message: format!("{} verification errors", counts.errors) }
            } else if counts.assumed > 0 {
                Verdict::Unknown {
                    reason: format!("{} functions assumed (not proven)", counts.assumed),
                }
            } else {
                Verdict::Unknown { reason: "verification inconclusive (exit code 2)".to_string() }
            }
        }
        3 => Verdict::Error { message: "contract parse errors".to_string() },
        _ => Verdict::Error { message: format!("unexpected exit code: {exit_code}") },
    }
}

/// Parse per-function verdicts from trust-wp's stdout.
///
/// trust_wp emits lines like:
///   `Verified: module::function (3/3 obligations)`
///   `Failed: module::function (1/3 obligations)`
fn parse_function_verdicts(stdout: &str, default_name: &str) -> Vec<FunctionVerdict> {
    let mut verdicts = Vec::new();

    for line in stdout.lines() {
        let trimmed = line.trim();

        let (verdict, rest) = if let Some(rest) = trimmed.strip_prefix("Verified: ") {
            (Verdict::Verified, rest)
        } else if let Some(rest) = trimmed.strip_prefix("Failed: ") {
            (Verdict::Failed, rest)
        } else if let Some(rest) = trimmed.strip_prefix("Error: ") {
            (Verdict::Error { message: rest.to_string() }, rest)
        } else {
            continue;
        };

        // Parse "function_name (N/M obligations)"
        let (name, obligations) = if let Some(paren_start) = rest.find('(') {
            let name = rest[..paren_start].trim().to_string();
            let obligation_str = &rest[paren_start..];
            let (discharged, total) = parse_obligation_counts(obligation_str);
            (name, (discharged, total))
        } else {
            (rest.trim().to_string(), (0, 0))
        };

        verdicts.push(FunctionVerdict {
            function_name: name,
            verdict,
            obligation_count: obligations.1,
            discharged_count: obligations.0,
            has_axiom_deps: false,
        });
    }

    // If no function verdicts parsed, create a default one
    if verdicts.is_empty() && !stdout.trim().is_empty() {
        verdicts.push(FunctionVerdict {
            function_name: default_name.to_string(),
            verdict: Verdict::Unknown {
                reason: "could not parse function-level verdicts".to_string(),
            },
            obligation_count: 0,
            discharged_count: 0,
            has_axiom_deps: false,
        });
    }

    verdicts
}

/// Parse "(N/M obligations)" from a verdict line.
fn parse_obligation_counts(s: &str) -> (u32, u32) {
    let inner = s.trim_start_matches('(').trim_end_matches(')').trim();
    if let Some(slash_pos) = inner.find('/') {
        let discharged = inner[..slash_pos].trim().parse::<u32>().unwrap_or(0);
        let rest = &inner[slash_pos + 1..];
        let total_str = rest.split_whitespace().next().unwrap_or("0");
        let total = total_str.parse::<u32>().unwrap_or(0);
        (discharged, total)
    } else {
        (0, 0)
    }
}

/// Parse inferred loop invariants from trust-wp's output.
///
/// trust_wp emits invariant candidates as:
///   `Invariant: loop@bb5 in module::function: x > 0 [confidence=0.95]`
fn parse_inferred_invariants(stdout: &str, default_function: &str) -> Vec<LoopInvariant> {
    let mut invariants = Vec::new();

    for line in stdout.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("Invariant: ")
            && let Some(inv) = parse_invariant_line(rest, default_function)
        {
            invariants.push(inv);
        }
    }

    invariants
}

/// Parse a single invariant line.
fn parse_invariant_line(line: &str, default_function: &str) -> Option<LoopInvariant> {
    // Expected format: "loop@bb5 in module::function: x > 0 [confidence=0.95]"
    let (loop_id, rest) = if let Some(in_pos) = line.find(" in ") {
        (line[..in_pos].to_string(), &line[in_pos + 4..])
    } else {
        return None;
    };

    let (function_name, rest) = if let Some(colon_pos) = rest.find(": ") {
        (rest[..colon_pos].to_string(), &rest[colon_pos + 2..])
    } else {
        (default_function.to_string(), line)
    };

    // Extract confidence from [confidence=X.XX] suffix
    let (expression, confidence, verified) = if let Some(bracket_pos) = rest.rfind('[') {
        let expr = rest[..bracket_pos].trim().to_string();
        let meta = &rest[bracket_pos..];
        let conf = extract_confidence(meta);
        let ver = meta.contains("verified");
        (expr, conf, ver)
    } else {
        (rest.trim().to_string(), 0.5, false)
    };

    Some(LoopInvariant { function_name, loop_id, expression, confidence, verified })
}

/// Extract confidence value from "[confidence=0.95]" or similar.
fn extract_confidence(meta: &str) -> f64 {
    if let Some(eq_pos) = meta.find("confidence=") {
        let rest = &meta[eq_pos + 11..];
        let end = rest.find(|c: char| !c.is_ascii_digit() && c != '.').unwrap_or(rest.len());
        rest[..end].parse::<f64>().unwrap_or(0.5)
    } else {
        0.5
    }
}

/// Parse key=value pairs from the wire line into counts.
fn parse_counts(rest: &str) -> VerificationCounts {
    let mut counts = VerificationCounts::default();

    for pair in rest.split_whitespace() {
        if let Some((key, value)) = pair.split_once('=') {
            let val: u64 = value.parse().unwrap_or(0);
            match key {
                "verified" => counts.verified = val,
                "failed" => counts.failed = val,
                "errors" => counts.errors = val,
                "warnings" => counts.warnings = val,
                "assumed" => counts.assumed = val,
                "trusted" => counts.trusted = val,
                "skipped" => counts.skipped = val,
                "verified_with_axiom_deps" => counts.verified_with_axiom_deps = val,
                _ => {} // Forward compatibility: ignore unknown keys
            }
        }
    }

    counts
}

#[cfg(test)]
mod tests {
    #[cfg(unix)]
    use std::os::unix::fs::PermissionsExt;

    use super::*;

    #[test]
    fn path_probe_is_scoped_to_each_backend() {
        let config = TrustWpConfig::new();
        let first = CliBackend::new_with_path_probe(&config, || Some("first".into()));
        let second = CliBackend::new_with_path_probe(&config, || Some("second".into()));
        assert_eq!(first.solver_path.as_deref(), Some("first"));
        assert_eq!(second.solver_path.as_deref(), Some("second"));

        let explicit = TrustWpConfig::new().with_solver_path("explicit");
        let backend = CliBackend::new_with_path_probe(&explicit, || {
            panic!("explicit configuration must not probe ambient executable authority")
        });
        assert_eq!(backend.solver_path.as_deref(), Some("explicit"));
    }
    use crate::contract::Contract;

    #[test]
    fn test_derive_verdict_exit_0_verified() {
        let counts = VerificationCounts { verified: 3, ..Default::default() };
        let verdict = derive_verdict(0, &counts, "");
        assert_eq!(verdict, Verdict::Verified);
    }

    #[test]
    fn test_derive_verdict_exit_0_with_soundness_gap_is_unknown() {
        // Trust #soundness (round-17): exit 0 but a structured counter reports a
        // soundness gap (assumed / axiom-dep / trusted / skipped) must NOT be a
        // full deductive Verified — fail closed to Unknown (defends against an
        // exit-code/wire-counter divergence).
        for counts in [
            VerificationCounts { verified: 2, assumed: 1, ..Default::default() },
            VerificationCounts { verified: 2, verified_with_axiom_deps: 1, ..Default::default() },
            VerificationCounts { verified: 2, trusted: 1, ..Default::default() },
            VerificationCounts { verified: 2, skipped: 1, ..Default::default() },
        ] {
            assert!(
                matches!(derive_verdict(0, &counts, ""), Verdict::Unknown { .. }),
                "exit 0 with a soundness gap must be Unknown, not Verified: {counts:?}"
            );
        }
        // No gap -> still Verified.
        let clean = VerificationCounts { verified: 3, ..Default::default() };
        assert_eq!(derive_verdict(0, &clean, ""), Verdict::Verified);
    }

    #[test]
    fn test_derive_verdict_exit_1_failed() {
        let counts = VerificationCounts { failed: 1, ..Default::default() };
        let verdict = derive_verdict(1, &counts, "");
        assert_eq!(verdict, Verdict::Failed);
    }

    #[test]
    fn test_derive_verdict_exit_2_errors() {
        let counts = VerificationCounts { errors: 2, ..Default::default() };
        let verdict = derive_verdict(2, &counts, "");
        assert!(matches!(verdict, Verdict::Error { .. }));
    }

    #[test]
    fn test_derive_verdict_exit_3_parse_errors() {
        let counts = VerificationCounts::default();
        let verdict = derive_verdict(3, &counts, "");
        assert!(matches!(verdict, Verdict::Error { .. }));
    }

    #[test]
    fn test_parse_wire_line_valid() {
        let stderr = "some output\nTRUST_WP_RESULT:v1 verified=5 failed=1 errors=0 warnings=2 assumed=0 trusted=1 skipped=0 verified_with_axiom_deps=0\nmore output\n";
        let counts = CliBackend::parse_wire_line(stderr).expect("should parse");
        assert_eq!(counts.verified, 5);
        assert_eq!(counts.failed, 1);
        assert_eq!(counts.warnings, 2);
        assert_eq!(counts.trusted, 1);
    }

    #[test]
    fn test_parse_wire_line_none() {
        let stderr = "no wire line here\njust regular output\n";
        assert!(CliBackend::parse_wire_line(stderr).is_none());
    }

    #[test]
    fn test_derive_verdict_exit_0_zero_counts_is_unknown() {
        // Trust #soundness (H1): a wire line that parses to ALL-ZERO counts
        // (e.g. a shim printing a bare "TRUST_WP_RESULT:v1") carries no
        // positive verification evidence; exit 0 must NOT become Verified.
        let verdict = derive_verdict(0, &VerificationCounts::default(), "");
        assert!(
            matches!(verdict, Verdict::Unknown { .. }),
            "exit 0 with zero verified obligations must be Unknown, got {verdict:?}"
        );
    }

    #[test]
    fn test_probe_honors_only_explicit_env_path_no_path_discovery() {
        // Trust #soundness (H1): the probe must NEVER fall back to `$PATH`
        // discovery. With no TRUST_WP_PATH configured it declines — even
        // though `which sh` (or a stray cargo-trust-wp) would succeed on any
        // dev machine. By construction the pure helper has no PATH branch.
        assert_eq!(probe_trust_wp_path_from(None), None);
        // A configured-but-missing path also declines (no silent fallback).
        assert_eq!(
            probe_trust_wp_path_from(Some("/nonexistent/trust-wp-h1-test".to_string())),
            None
        );
        // An empty configuration declines.
        assert_eq!(probe_trust_wp_path_from(Some(String::new())), None);
        // An explicitly-configured EXISTING path is honored.
        let dir = std::env::temp_dir();
        let existing = dir.to_string_lossy().to_string();
        assert_eq!(probe_trust_wp_path_from(Some(existing.clone())), Some(existing));
    }

    /// Trust #soundness (H1) — THE LANDMINE TRAP. A binary that prints usage
    /// text and exits 0 for any args (exactly the in-tree `trust-wp-driver`
    /// placeholder) must NOT yield Verified/Proved: no wire line ⇒ Unknown.
    #[cfg(unix)]
    #[test]
    fn test_verify_fake_exit0_binary_without_wire_line_is_unknown() {
        let script = write_test_script(
            "fake-placeholder",
            "#!/bin/sh\necho 'Use `cargo trust-wp` for normal verification.' >&2\nexit 0\n",
        );
        let config = TrustWpConfig::new().with_solver_path(script.to_string_lossy().as_ref());
        let backend = CliBackend::new(&config);

        let result = backend
            .verify("my::func", &ContractSet::new())
            .expect("fake binary run is representable");
        let _ = std::fs::remove_file(script);

        assert!(
            matches!(result.verdict, Verdict::Unknown { .. }),
            "exit-0 binary with no wire line must be Unknown, got {:?}",
            result.verdict
        );
        assert!(
            !result.to_verification_result().is_proved(),
            "a placeholder binary must never mint a Proved"
        );
    }

    /// Trust #soundness (H1): a shim emitting a BARE wire line (all counts
    /// missing ⇒ all-zero) with exit 0 must also fail closed to Unknown.
    #[cfg(unix)]
    #[test]
    fn test_verify_bare_wire_line_zero_counts_is_unknown() {
        let script =
            write_test_script("bare-wire", "#!/bin/sh\necho 'TRUST_WP_RESULT:v1' >&2\nexit 0\n");
        let config = TrustWpConfig::new().with_solver_path(script.to_string_lossy().as_ref());
        let backend = CliBackend::new(&config);

        let result = backend
            .verify("my::func", &ContractSet::new())
            .expect("bare wire line run is representable");
        let _ = std::fs::remove_file(script);

        assert!(
            matches!(result.verdict, Verdict::Unknown { .. }),
            "bare wire line (zero counts) must be Unknown, got {:?}",
            result.verdict
        );
        assert!(!result.to_verification_result().is_proved());
    }

    /// Positive control for the H1 hardening: a well-formed wire line with
    /// verified>=1 and no soundness gap still yields Verified (the legitimate
    /// path is not broken by the fail-closed changes).
    #[cfg(unix)]
    #[test]
    fn test_verify_wire_line_with_evidence_still_verifies() {
        let script = write_test_script(
            "good-wire",
            "#!/bin/sh\necho 'TRUST_WP_RESULT:v1 verified=1 failed=0 errors=0 warnings=0 assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0' >&2\nexit 0\n",
        );
        let config = TrustWpConfig::new().with_solver_path(script.to_string_lossy().as_ref());
        let backend = CliBackend::new(&config);

        let result = backend
            .verify("my::func", &ContractSet::new())
            .expect("well-formed run is representable");
        let _ = std::fs::remove_file(script);

        assert_eq!(result.verdict, Verdict::Verified);
        assert_eq!(result.counts.verified, 1);
    }

    #[test]
    fn test_parse_function_verdicts() {
        let stdout = "Verified: my::module::func (3/3 obligations)\nFailed: my::module::bad_func (1/5 obligations)\n";
        let verdicts = parse_function_verdicts(stdout, "default");
        assert_eq!(verdicts.len(), 2);
        assert_eq!(verdicts[0].function_name, "my::module::func");
        assert_eq!(verdicts[0].verdict, Verdict::Verified);
        assert_eq!(verdicts[0].discharged_count, 3);
        assert_eq!(verdicts[0].obligation_count, 3);
        assert_eq!(verdicts[1].function_name, "my::module::bad_func");
        assert_eq!(verdicts[1].verdict, Verdict::Failed);
        assert_eq!(verdicts[1].discharged_count, 1);
        assert_eq!(verdicts[1].obligation_count, 5);
    }

    #[test]
    fn test_parse_function_verdicts_empty() {
        let verdicts = parse_function_verdicts("", "default");
        assert!(verdicts.is_empty());
    }

    #[test]
    fn test_parse_obligation_counts() {
        assert_eq!(parse_obligation_counts("(3/5 obligations)"), (3, 5));
        assert_eq!(parse_obligation_counts("(0/0)"), (0, 0));
        assert_eq!(parse_obligation_counts("invalid"), (0, 0));
    }

    #[test]
    fn test_parse_inferred_invariants() {
        let stdout = "Invariant: loop@bb5 in my::func: x > 0 [confidence=0.95]\nInvariant: loop@bb8 in my::func: y >= 0 [confidence=0.80, verified]\n";
        let invariants = parse_inferred_invariants(stdout, "my::func");
        assert_eq!(invariants.len(), 2);
        assert_eq!(invariants[0].loop_id, "loop@bb5");
        assert_eq!(invariants[0].expression, "x > 0");
        assert!((invariants[0].confidence - 0.95).abs() < f64::EPSILON);
        assert!(!invariants[0].verified);
        assert_eq!(invariants[1].loop_id, "loop@bb8");
        assert!(invariants[1].verified);
    }

    #[test]
    fn test_parse_inferred_invariants_empty() {
        let invariants = parse_inferred_invariants("no invariants here", "func");
        assert!(invariants.is_empty());
    }

    #[test]
    fn test_extract_confidence() {
        assert!((extract_confidence("[confidence=0.95]") - 0.95).abs() < f64::EPSILON);
        assert!((extract_confidence("[confidence=1.0, verified]") - 1.0).abs() < f64::EPSILON);
        assert!((extract_confidence("[no confidence]") - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_parse_counts() {
        let counts = parse_counts(
            "verified=3 failed=1 errors=0 warnings=0 assumed=0 trusted=0 skipped=2 verified_with_axiom_deps=0",
        );
        assert_eq!(counts.verified, 3);
        assert_eq!(counts.failed, 1);
        assert_eq!(counts.skipped, 2);
    }

    #[test]
    fn test_parse_counts_unknown_keys() {
        let counts = parse_counts("verified=1 future_field=42");
        assert_eq!(counts.verified, 1);
    }

    #[test]
    fn test_parse_diagnostics() {
        let stderr = "TRUST_WP_RESULT:v1 verified=1\nerror: something failed\nwarning: check this\nnote here\n";
        let diags = CliBackend::parse_diagnostics(stderr);
        assert_eq!(diags.len(), 3); // wire line excluded
        assert_eq!(diags[0].level, DiagLevel::Error);
        assert_eq!(diags[1].level, DiagLevel::Warning);
        assert_eq!(diags[2].level, DiagLevel::Note);
    }

    #[test]
    fn test_build_verify_args() {
        let config = TrustWpConfig::new().with_track_level("mem");
        let backend = CliBackend::new(&config);
        let contracts = ContractSet::new()
            .with_requires(Contract::requires("x > 0"))
            .with_ensures(Contract::ensures("result >= x"));
        let args = backend.build_verify_args("my::func", &contracts);
        assert!(args.contains(&"--function".to_string()));
        assert!(args.contains(&"my::func".to_string()));
        assert!(args.contains(&"--track".to_string()));
        assert!(args.contains(&"mem".to_string()));
        assert!(args.contains(&"--requires".to_string()));
        assert!(args.contains(&"x > 0".to_string()));
        assert!(args.contains(&"--ensures".to_string()));
        assert!(args.contains(&"result >= x".to_string()));
    }

    #[cfg(unix)]
    fn write_test_script(name: &str, body: &str) -> std::path::PathBuf {
        let path = std::env::temp_dir().join(format!(
            "trust-wp-{name}-{}-{}.sh",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        std::fs::write(&path, body).expect("write test script");
        let mut perms = std::fs::metadata(&path).expect("test script metadata").permissions();
        perms.set_mode(0o700);
        std::fs::set_permissions(&path, perms).expect("chmod test script");
        path
    }

    #[cfg(unix)]
    #[test]
    fn test_run_subprocess_kills_after_timeout() {
        let script = write_test_script("timeout", "#!/bin/sh\nsleep 2 &\nwait\n");
        let config = TrustWpConfig::new()
            .with_solver_path(script.to_string_lossy().as_ref())
            .with_timeout(50);
        let backend = CliBackend::new(&config);

        let start = Instant::now();
        let output = backend.run_subprocess(&[]).expect("subprocess should be killed cleanly");
        let elapsed = start.elapsed();
        let _ = std::fs::remove_file(script);

        assert!(output.timed_out);
        assert!(elapsed < Duration::from_secs(1));
    }

    #[cfg(unix)]
    #[test]
    fn test_verify_returns_timeout_verdict_for_hung_subprocess() {
        let script = write_test_script("verify-timeout", "#!/bin/sh\nsleep 2 &\nwait\n");
        let config = TrustWpConfig::new()
            .with_solver_path(script.to_string_lossy().as_ref())
            .with_timeout(50);
        let backend = CliBackend::new(&config);

        let result = backend
            .verify("my::func", &ContractSet::new())
            .expect("timeout is represented as a trust_wp result");
        let _ = std::fs::remove_file(script);

        assert_eq!(result.verdict, Verdict::Timeout);
        assert!(result.time_ms < 1_000);
        assert_eq!(result.function_name, "my::func");
    }

    #[test]
    fn test_contract_set_builder() {
        let contracts = ContractSet::new()
            .with_requires(Contract::requires("x > 0"))
            .with_requires(Contract::requires("y != 0"))
            .with_ensures(Contract::ensures("result == x / y"))
            .with_invariant(Contract::invariant("i < n"))
            .with_trusted(false);
        assert_eq!(contracts.requires.len(), 2);
        assert_eq!(contracts.ensures.len(), 1);
        assert_eq!(contracts.invariants.len(), 1);
        assert!(!contracts.trusted);
        assert_eq!(contracts.len(), 4);
        assert!(!contracts.is_empty());
    }

    #[test]
    fn test_contract_set_empty() {
        let contracts = ContractSet::new();
        assert!(contracts.is_empty());
        assert_eq!(contracts.len(), 0);
    }

    #[test]
    fn test_trust_wp_result_verdict_helpers() {
        let verified = TrustWpResult {
            verdict: Verdict::Verified,
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 100,
            diagnostics: Vec::new(),
            function_name: "test".to_string(),
            counts: VerificationCounts::default(),
        };
        assert!(verified.is_verified());
        assert!(!verified.is_failed());
        assert!(!verified.is_unknown());

        let failed = TrustWpResult {
            verdict: Verdict::Failed,
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 100,
            diagnostics: Vec::new(),
            function_name: "test".to_string(),
            counts: VerificationCounts::default(),
        };
        assert!(!failed.is_verified());
        assert!(failed.is_failed());

        let unknown = TrustWpResult {
            verdict: Verdict::Unknown { reason: "test".to_string() },
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 100,
            diagnostics: Vec::new(),
            function_name: "test".to_string(),
            counts: VerificationCounts::default(),
        };
        assert!(unknown.is_unknown());
    }

    #[test]
    fn test_trust_wp_result_to_verification_result_verified() {
        let result = TrustWpResult {
            verdict: Verdict::Verified,
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 42,
            diagnostics: Vec::new(),
            function_name: "test_fn".to_string(),
            counts: VerificationCounts::default(),
        };
        let vr = result.to_verification_result();
        assert!(vr.is_proved());
        assert_eq!(vr.solver_name(), "trust-wp-lib");
        assert_eq!(vr.time_ms(), 42);
    }

    #[test]
    fn test_trust_wp_result_to_verification_result_failed() {
        let result = TrustWpResult {
            verdict: Verdict::Failed,
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 15,
            diagnostics: Vec::new(),
            function_name: "test_fn".to_string(),
            counts: VerificationCounts::default(),
        };
        let vr = result.to_verification_result();
        assert!(vr.is_failed());
        assert_eq!(vr.solver_name(), "trust-wp-lib");
    }

    #[test]
    fn test_trust_wp_result_to_verification_result_timeout() {
        let result = TrustWpResult {
            verdict: Verdict::Timeout,
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 60_000,
            diagnostics: Vec::new(),
            function_name: "test_fn".to_string(),
            counts: VerificationCounts::default(),
        };
        let vr = result.to_verification_result();
        assert!(matches!(vr, trust_types::VerificationResult::Timeout { .. }));
    }

    #[test]
    fn test_trust_wp_config_builder() {
        let config = TrustWpConfig::new()
            .with_timeout(120_000)
            .with_solver_path("/usr/local/bin/trust-wp")
            .with_diagnostics(DiagConfig::Capture)
            .with_proofs(true)
            .with_track_level("mem")
            .with_infer_invariants(true);

        assert_eq!(config.timeout_ms, 120_000);
        assert_eq!(config.solver_path.as_deref(), Some("/usr/local/bin/trust-wp"));
        assert_eq!(config.diagnostics, DiagConfig::Capture);
        assert!(config.produce_proofs);
        assert_eq!(config.track_level, "mem");
        assert!(config.infer_invariants);
    }
}
