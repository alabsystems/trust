// trust-bmc subprocess backend
//
// Compatibility implementation: delegates to trust_mc CLI via subprocess.
// Target tRustc builds replace this with direct in-process integration.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Subprocess-based trust_mc backend.
//!
//! Invokes trust_mc as a subprocess, communicating via SMT-LIB2 over stdin/stdout.
//! This compatibility path is BMC-shaped and cannot represent trust-mc's full
//! CHC/PDR proof modes. Target tRustc builds call trust-mc's codegen_ay in-process.

use std::collections::BTreeMap;
use std::io::{Read as _, Write as _};
use std::process::{Child, Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use crate::config::{DiagConfig, TrustMcConfig};
use crate::error::TrustMcLibError;
use crate::result::{
    DiagLevel, DiagnosticMessage, TraceStep, TrustMcProofMode, TrustMcProofProvenance,
    TrustMcResult, TypedCounterexample, TypedValue, Verdict, ViolationInfo,
};

/// Probe for the trust_mc binary.
///
/// Priority: `TRUST_MC_PATH` env var > `trust-mc` on PATH.
fn probe_trust_mc_path() -> Option<String> {
    if let Ok(path) = std::env::var("TRUST_MC_PATH")
        && std::path::Path::new(&path).exists()
    {
        return Some(path);
    }

    if let Ok(output) = Command::new("which").arg("trust-mc").output()
        && output.status.success()
    {
        let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
        if !path.is_empty() {
            return Some(path);
        }
    }

    None
}

/// Subprocess-based trust_mc backend.
///
/// Communicates with trust_mc via SMT-LIB2 over stdin/stdout. This is the
/// Compatibility implementation that is superseded by direct in-process
/// integration when the `trust-build` feature is enabled.
pub struct SubprocessBackend {
    /// Resolved solver path.
    solver_path: Option<String>,
    /// Extra solver arguments.
    solver_args: Vec<String>,
    /// Timeout in milliseconds.
    timeout_ms: u64,
    /// BMC depth.
    bmc_depth: u32,
    /// Proof mode attached to this BMC-shaped compatibility solve.
    proof_mode: TrustMcProofMode,
    /// Diagnostic configuration.
    diag_config: DiagConfig,
    /// Whether to produce models.
    produce_models: bool,
}

impl SubprocessBackend {
    /// Create a new subprocess backend from config.
    pub(crate) fn new(config: &TrustMcConfig) -> Self {
        Self::new_with_path_probe(config, probe_trust_mc_path)
    }

    fn new_with_path_probe(config: &TrustMcConfig, probe: impl FnOnce() -> Option<String>) -> Self {
        Self {
            // Resolve ambient configuration once per backend, not once per
            // process. Long-lived compiler/library hosts may create multiple
            // verification sessions with different TRUST_MC_PATH/PATH values;
            // a process-global OnceLock made the first session's executable
            // authority leak permanently into every later session.
            solver_path: config.solver_path.clone().or_else(probe),
            solver_args: config.solver_args.clone(),
            timeout_ms: config.timeout_ms,
            bmc_depth: config.bmc_depth,
            proof_mode: config.proof_mode,
            diag_config: config.diagnostics.clone(),
            produce_models: config.produce_models,
        }
    }

    /// Resolve the solver path captured for this backend/session.
    fn resolve_path(&self) -> Result<&str, TrustMcLibError> {
        self.solver_path.as_deref().ok_or_else(|| TrustMcLibError::BinaryNotFound {
            reason: "set TRUST_MC_PATH env or install trust_mc on PATH".to_string(),
        })
    }

    /// Run trust_mc on an SMT-LIB2 script and return raw stdout + stderr.
    fn run_solver(&self, script: &str) -> Result<SolverRun, TrustMcLibError> {
        let path = self.resolve_path()?;

        let mut command = Command::new(path);
        command
            .args(&self.solver_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        // Own process group: a solver that forks must die with its deadline,
        // or its children keep the captured pipes open and the join below
        // blocks past the timeout it was supposed to enforce.
        let mut child = trust_os::spawn_in_own_process_group(&mut command)?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(script.as_bytes())
                .map_err(|e| TrustMcLibError::InputError { reason: e.to_string() })?;
        }

        wait_with_timeout(child, Duration::from_millis(self.timeout_ms))
    }

    fn timeout_result(
        &self,
        function_name: &str,
        elapsed: u64,
        diagnostics: Vec<DiagnosticMessage>,
    ) -> TrustMcResult {
        TrustMcResult {
            verdict: Verdict::Timeout,
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            proof_mode: self.proof_mode,
            proof_provenance: Some(self.proof_provenance()),
            time_ms: elapsed,
            diagnostics,
            bmc_depth: self.bmc_depth,
            function_name: function_name.to_string(),
        }
    }

    /// Verify a function using the subprocess backend.
    pub(crate) fn verify(
        &self,
        function_name: &str,
        smtlib_script: &str,
    ) -> Result<TrustMcResult, TrustMcLibError> {
        let start = Instant::now();

        // Generate the BMC-wrapped script
        let script = self.wrap_bmc_script(smtlib_script);

        // Run the solver
        let run = self.run_solver(&script)?;
        let elapsed = start.elapsed().as_millis() as u64;

        // Parse diagnostics from stderr
        let diagnostics = if self.diag_config == DiagConfig::Capture {
            parse_diagnostics(&run.stderr)
        } else {
            Vec::new()
        };

        // Check for timeout
        if run.timed_out || elapsed >= self.timeout_ms {
            return Ok(self.timeout_result(function_name, elapsed, diagnostics));
        }

        // Parse the result
        let (verdict, counterexample, violations) =
            parse_solver_output(&run.stdout, self.bmc_depth);

        Ok(TrustMcResult {
            verdict,
            counterexample,
            proof_certificate: None,
            violations,
            proof_mode: self.proof_mode,
            proof_provenance: Some(self.proof_provenance()),
            time_ms: elapsed,
            diagnostics,
            bmc_depth: self.bmc_depth,
            function_name: function_name.to_string(),
        })
    }

    /// Wrap an SMT-LIB2 script with BMC-specific options for trust_mc.
    fn wrap_bmc_script(&self, base_script: &str) -> String {
        let mut script = String::with_capacity(base_script.len() + 128);
        script.push_str("; trust-mc-lib BMC configuration\n");
        if self.produce_models {
            script.push_str("(set-option :produce-models true)\n");
        }
        script.push_str(&format!("(set-option :bmc-depth {})\n", self.bmc_depth));
        script.push_str(base_script);
        script
    }

    fn proof_provenance(&self) -> TrustMcProofProvenance {
        match self.proof_mode {
            TrustMcProofMode::Bmc => {
                TrustMcProofProvenance::bmc(self.bmc_depth, "trust-bmc-subprocess")
            }
            TrustMcProofMode::FiniteAcyclicBmc => {
                TrustMcProofProvenance::finite_acyclic_bmc(self.bmc_depth, "trust-bmc-subprocess")
            }
            TrustMcProofMode::Chc | TrustMcProofMode::PdrIc3 => {
                TrustMcProofProvenance::unbounded(self.proof_mode, "trust-bmc-subprocess")
            }
        }
    }
}

struct SolverRun {
    stdout: String,
    stderr: String,
    timed_out: bool,
}

fn wait_with_timeout(mut child: Child, timeout: Duration) -> Result<SolverRun, TrustMcLibError> {
    let stdout_reader = child.stdout.take().map(|mut stdout| {
        thread::spawn(move || {
            let mut buf = Vec::new();
            stdout.read_to_end(&mut buf).map(|_| buf)
        })
    });
    let stderr_reader = child.stderr.take().map(|mut stderr| {
        thread::spawn(move || {
            let mut buf = Vec::new();
            stderr.read_to_end(&mut buf).map(|_| buf)
        })
    });

    let timed_out = trust_os::wait_bounded(&mut child, timeout)?.timed_out;

    let stdout = join_output_reader(stdout_reader)?;
    let stderr = join_output_reader(stderr_reader)?;

    Ok(SolverRun { stdout, stderr, timed_out })
}

fn join_output_reader(
    reader: Option<thread::JoinHandle<std::io::Result<Vec<u8>>>>,
) -> Result<String, TrustMcLibError> {
    let Some(reader) = reader else {
        return Ok(String::new());
    };

    let bytes = reader.join().map_err(|_| TrustMcLibError::InputError {
        reason: "trust-mc output reader thread panicked".to_string(),
    })??;

    Ok(String::from_utf8_lossy(&bytes).to_string())
}

/// Parse solver stdout into verdict, counterexample, and violations.
fn parse_solver_output(
    output: &str,
    bmc_depth: u32,
) -> (Verdict, Option<TypedCounterexample>, Vec<ViolationInfo>) {
    let trimmed = output.trim();

    if trimmed.starts_with("unsat") {
        return (Verdict::Proved, None, Vec::new());
    }

    if trimmed.starts_with("sat") {
        let cex = parse_counterexample(trimmed);
        let violations = Vec::new(); // Violations parsed from model in Phase 2
        return (Verdict::Failed, cex, violations);
    }

    if trimmed.starts_with("unknown") {
        let is_bound_exhausted =
            trimmed.contains("bound") || trimmed.contains("depth") || trimmed.contains("resource");

        let reason = if is_bound_exhausted {
            format!("BMC bound exhausted at depth {bmc_depth}")
        } else {
            "solver returned unknown".to_string()
        };

        return (Verdict::Unknown { reason }, None, Vec::new());
    }

    (
        Verdict::Unknown {
            reason: format!("unexpected solver output: {}", &trimmed[..trimmed.len().min(200)]),
        },
        None,
        Vec::new(),
    )
}

/// Parse a counterexample from solver SAT output.
fn parse_counterexample(output: &str) -> Option<TypedCounterexample> {
    let mut variables = BTreeMap::new();
    let mut trace_steps: Vec<(u32, BTreeMap<String, TypedValue>)> = Vec::new();

    for line in output.lines() {
        let trimmed = line.trim();
        if !trimmed.contains("define-fun") {
            continue;
        }

        if let Some((name, value)) = parse_define_fun(trimmed) {
            // Check for step-indexed variables (e.g., "x_step_3")
            if let Some((base_name, step)) = extract_step_index(&name) {
                let entry = trace_steps.iter_mut().find(|(s, _)| *s == step);
                if let Some((_, assigns)) = entry {
                    assigns.insert(base_name, value.clone());
                } else {
                    let mut map = BTreeMap::new();
                    map.insert(base_name, value.clone());
                    trace_steps.push((step, map));
                }
            }
            variables.insert(name, value);
        }
    }

    if variables.is_empty() {
        return None;
    }

    let trace = if trace_steps.len() > 1 {
        trace_steps.sort_by_key(|(step, _)| *step);
        Some(
            trace_steps
                .into_iter()
                .map(|(step, assignments)| TraceStep { step, assignments, program_point: None })
                .collect(),
        )
    } else {
        None
    };

    let mut cex = TypedCounterexample::new(variables);
    if let Some(trace) = trace {
        cex = cex.with_trace(trace);
    }
    Some(cex)
}

/// Parse a single `(define-fun name () Sort value)` line.
fn parse_define_fun(line: &str) -> Option<(String, TypedValue)> {
    let content = line.trim().trim_start_matches('(');
    let rest = content.strip_prefix("define-fun ")?;

    let name_end = rest.find(|c: char| c.is_whitespace())?;
    let name = rest[..name_end].to_string();
    let rest = rest[name_end..].trim();

    // Skip "()" parameter list
    let rest = rest.strip_prefix("()")?.trim();

    // Parse sort
    let (sort_str, rest) = if rest.starts_with('(') {
        let depth = find_matching_paren(rest)?;
        (&rest[..=depth], rest[depth + 1..].trim())
    } else {
        let end = rest.find(|c: char| c.is_whitespace())?;
        (&rest[..end], rest[end..].trim())
    };

    let value_str = rest.trim_end_matches(')').trim();
    let value = parse_model_value(sort_str, value_str)?;

    Some((name, value))
}

/// Find the index of the matching closing paren.
fn find_matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Parse a model value given its SMT-LIB2 sort and value string.
fn parse_model_value(sort_str: &str, value_str: &str) -> Option<TypedValue> {
    if sort_str == "Bool" {
        return match value_str {
            "true" => Some(TypedValue::Bool(true)),
            "false" => Some(TypedValue::Bool(false)),
            _ => None,
        };
    }

    if sort_str == "Int" {
        return parse_int_value(value_str);
    }

    if sort_str.contains("BitVec") {
        // Extract width from (_ BitVec N)
        let width = sort_str
            .trim_start_matches("(_ BitVec ")
            .trim_end_matches(')')
            .trim()
            .parse::<u32>()
            .unwrap_or(64);
        return parse_bv_value(value_str, width);
    }

    // Fallback: store as string
    Some(TypedValue::String(value_str.to_string()))
}

/// Parse an integer value, handling SMT-LIB2 negation syntax `(- N)`.
fn parse_int_value(s: &str) -> Option<TypedValue> {
    let s = s.trim();
    if s.starts_with("(-") || s.starts_with("(- ") {
        let inner = s.trim_start_matches('(').trim_start_matches('-').trim().trim_end_matches(')');
        let n: i128 = inner.parse().ok()?;
        Some(TypedValue::Int(-n))
    } else if let Ok(n) = s.parse::<u128>() {
        Some(TypedValue::Uint(n))
    } else if let Ok(n) = s.parse::<i128>() {
        Some(TypedValue::Int(n))
    } else {
        None
    }
}

/// Parse a bitvector value like `#x0000000a` or `#b1010` or `(_ bv10 32)`.
fn parse_bv_value(s: &str, width: u32) -> Option<TypedValue> {
    let s = s.trim();
    if let Some(hex) = s.strip_prefix("#x") {
        let value = u128::from_str_radix(hex, 16).ok()?;
        Some(TypedValue::BitVec { value, width })
    } else if let Some(bin) = s.strip_prefix("#b") {
        let value = u128::from_str_radix(bin, 2).ok()?;
        Some(TypedValue::BitVec { value, width })
    } else if s.starts_with("(_ bv") {
        let inner = s.trim_start_matches("(_ bv").trim_end_matches(')');
        let parts: Vec<&str> = inner.split_whitespace().collect();
        if let Some(val_str) = parts.first() {
            let value: u128 = val_str.parse().ok()?;
            Some(TypedValue::BitVec { value, width })
        } else {
            None
        }
    } else {
        None
    }
}

/// Extract step index from a step-indexed variable name.
fn extract_step_index(name: &str) -> Option<(String, u32)> {
    let parts: Vec<&str> = name.rsplitn(2, "_step_").collect();
    if parts.len() == 2 {
        let step: u32 = parts[0].parse().ok()?;
        Some((parts[1].to_string(), step))
    } else {
        None
    }
}

/// Parse diagnostic messages from stderr.
fn parse_diagnostics(stderr: &str) -> Vec<DiagnosticMessage> {
    stderr
        .lines()
        .filter(|line| !line.trim().is_empty())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_probe_is_scoped_to_each_backend() {
        let config = TrustMcConfig::new();
        let first = SubprocessBackend::new_with_path_probe(&config, || Some("first".into()));
        let second = SubprocessBackend::new_with_path_probe(&config, || Some("second".into()));
        assert_eq!(first.solver_path.as_deref(), Some("first"));
        assert_eq!(second.solver_path.as_deref(), Some("second"));

        let explicit = TrustMcConfig::new().with_solver_path("explicit");
        let backend = SubprocessBackend::new_with_path_probe(&explicit, || {
            panic!("explicit configuration must not probe ambient executable authority")
        });
        assert_eq!(backend.solver_path.as_deref(), Some("explicit"));
    }

    #[cfg(unix)]
    #[test]
    fn test_verify_kills_hung_subprocess_on_timeout() {
        let config = TrustMcConfig::new()
            .with_solver_path("/bin/sh")
            .with_timeout(50)
            .with_bmc_depth(17)
            .with_diagnostics(DiagConfig::Capture);
        let mut backend = SubprocessBackend::new(&config);
        backend.solver_args =
            vec!["-c".to_string(), "echo 'warning: still running' >&2; exec sleep 5".to_string()];

        let start = Instant::now();
        let result = backend
            .verify("hung_fn", "(assert true)\n(check-sat)\n")
            .expect("timeout should be returned as a TrustMcResult");

        assert!(
            start.elapsed() < Duration::from_secs(2),
            "hung subprocess should be killed promptly"
        );
        assert_eq!(result.verdict, Verdict::Timeout);
        assert_eq!(result.proof_mode, TrustMcProofMode::Bmc);
        assert_eq!(result.bmc_depth, 17);
        assert_eq!(result.function_name, "hung_fn");
        assert!(result.time_ms >= 50);
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].level, DiagLevel::Warning);
    }

    #[test]
    fn test_parse_solver_output_unsat() {
        let (verdict, cex, violations) = parse_solver_output("unsat\n", 100);
        assert_eq!(verdict, Verdict::Proved);
        assert!(cex.is_none());
        assert!(violations.is_empty());
    }

    #[test]
    fn test_parse_solver_output_sat_with_model() {
        let output = "sat\n(model\n  (define-fun x () Int 42)\n  (define-fun y () Bool false)\n)\n";
        let (verdict, cex, _) = parse_solver_output(output, 100);
        assert_eq!(verdict, Verdict::Failed);
        let cex = cex.expect("should have counterexample");
        assert_eq!(cex.variables.len(), 2);
        assert_eq!(cex.variables["x"], TypedValue::Uint(42));
        assert_eq!(cex.variables["y"], TypedValue::Bool(false));
    }

    #[test]
    fn test_parse_solver_output_sat_no_model() {
        let (verdict, cex, _) = parse_solver_output("sat\n", 100);
        assert_eq!(verdict, Verdict::Failed);
        assert!(cex.is_none());
    }

    #[test]
    fn test_parse_solver_output_unknown_bound_exhausted() {
        let output = "unknown\nbound limit reached\n";
        let (verdict, _, _) = parse_solver_output(output, 500);
        match verdict {
            Verdict::Unknown { reason } => {
                assert!(reason.contains("BMC bound exhausted at depth 500"));
            }
            _ => panic!("expected Unknown"),
        }
    }

    #[test]
    fn test_parse_solver_output_unknown_generic() {
        let (verdict, _, _) = parse_solver_output("unknown\n", 50);
        match verdict {
            Verdict::Unknown { reason } => {
                assert_eq!(reason, "solver returned unknown");
            }
            _ => panic!("expected Unknown"),
        }
    }

    #[test]
    fn test_parse_solver_output_unexpected() {
        let (verdict, _, _) = parse_solver_output("(error \"bad logic\")\n", 50);
        assert!(matches!(verdict, Verdict::Unknown { .. }));
    }

    #[test]
    fn test_parse_counterexample_int_and_bool() {
        let output = "sat\n(model\n  (define-fun a () Int 10)\n  (define-fun b () Bool true)\n)\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert_eq!(cex.variables.len(), 2);
        assert_eq!(cex.variables["a"], TypedValue::Uint(10));
        assert_eq!(cex.variables["b"], TypedValue::Bool(true));
        assert!(cex.trace.is_none());
    }

    #[test]
    fn test_parse_counterexample_negative_int() {
        let output = "sat\n(model\n  (define-fun x () Int (- 5))\n)\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert_eq!(cex.variables["x"], TypedValue::Int(-5));
    }

    #[test]
    fn test_parse_counterexample_bitvector() {
        let output = "sat\n(model\n  (define-fun ptr () (_ BitVec 64) #xdeadbeef00000000)\n)\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert_eq!(
            cex.variables["ptr"],
            TypedValue::BitVec { value: 0xdeadbeef00000000, width: 64 }
        );
    }

    #[test]
    fn test_parse_counterexample_binary_bitvector() {
        let output = "sat\n(model\n  (define-fun bits () (_ BitVec 8) #b11111111)\n)\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert_eq!(cex.variables["bits"], TypedValue::BitVec { value: 255, width: 8 });
    }

    #[test]
    fn test_parse_counterexample_with_trace() {
        let output = "sat\n\
            (model\n\
              (define-fun x_step_0 () Int 10)\n\
              (define-fun x_step_1 () Int 5)\n\
              (define-fun x_step_2 () Int 0)\n\
            )\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert_eq!(cex.variables.len(), 3);
        let trace = cex.trace.as_ref().expect("should have trace");
        assert_eq!(trace.len(), 3);
        assert_eq!(trace[0].step, 0);
        assert_eq!(trace[1].step, 1);
        assert_eq!(trace[2].step, 2);
    }

    #[test]
    fn test_parse_counterexample_single_step_no_trace() {
        let output = "sat\n(model\n  (define-fun x_step_0 () Int 10)\n)\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert!(cex.trace.is_none(), "single step should not produce trace");
    }

    #[test]
    fn test_parse_counterexample_empty_model() {
        let output = "sat\n(model\n)\n";
        assert!(parse_counterexample(output).is_none());
    }

    #[test]
    fn test_extract_step_index_valid() {
        let (base, step) = extract_step_index("x_step_3").expect("should parse");
        assert_eq!(base, "x");
        assert_eq!(step, 3);
    }

    #[test]
    fn test_extract_step_index_invalid() {
        assert!(extract_step_index("x").is_none());
        assert!(extract_step_index("x_step_").is_none());
        assert!(extract_step_index("x_step_abc").is_none());
    }

    #[test]
    fn test_parse_diagnostics() {
        let stderr = "error: something failed\nwarning: check this\nnote: fyi\n";
        let diags = parse_diagnostics(stderr);
        assert_eq!(diags.len(), 3);
        assert_eq!(diags[0].level, DiagLevel::Error);
        assert_eq!(diags[1].level, DiagLevel::Warning);
        assert_eq!(diags[2].level, DiagLevel::Note);
    }

    #[test]
    fn test_trust_mc_result_verdict_helpers() {
        let proved = TrustMcResult {
            verdict: Verdict::Proved,
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            proof_mode: TrustMcProofMode::Bmc,
            proof_provenance: Some(TrustMcProofProvenance::bmc(100, "test")),
            time_ms: 10,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test".to_string(),
        };
        assert!(proved.is_proved());
        assert!(!proved.is_failed());
        assert!(!proved.is_unknown());

        let failed = TrustMcResult {
            verdict: Verdict::Failed,
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            proof_mode: TrustMcProofMode::Bmc,
            proof_provenance: Some(TrustMcProofProvenance::bmc(100, "test")),
            time_ms: 10,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test".to_string(),
        };
        assert!(!failed.is_proved());
        assert!(failed.is_failed());

        let unknown = TrustMcResult {
            verdict: Verdict::Unknown { reason: "test".to_string() },
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            proof_mode: TrustMcProofMode::Bmc,
            proof_provenance: Some(TrustMcProofProvenance::bmc(100, "test")),
            time_ms: 10,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test".to_string(),
        };
        assert!(unknown.is_unknown());
    }

    #[test]
    fn test_trust_mc_result_to_verification_result_proved() {
        let result = TrustMcResult {
            verdict: Verdict::Proved,
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            proof_mode: TrustMcProofMode::Bmc,
            proof_provenance: Some(TrustMcProofProvenance::bmc(100, "test")),
            time_ms: 42,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test_fn".to_string(),
        };
        let vr = result.to_verification_result();
        assert!(vr.is_proved());
        assert_eq!(vr.solver_name(), "trust-mc-lib");
        assert_eq!(vr.time_ms(), 42);
    }

    #[test]
    fn test_trust_mc_result_to_verification_result_failed() {
        let mut vars = BTreeMap::new();
        vars.insert("x".to_string(), TypedValue::Uint(0));
        let result = TrustMcResult {
            verdict: Verdict::Failed,
            counterexample: Some(TypedCounterexample::new(vars)),
            proof_certificate: None,
            violations: Vec::new(),
            proof_mode: TrustMcProofMode::Bmc,
            proof_provenance: Some(TrustMcProofProvenance::bmc(100, "test")),
            time_ms: 15,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test_fn".to_string(),
        };
        let vr = result.to_verification_result();
        assert!(vr.is_failed());
        assert_eq!(vr.solver_name(), "trust-mc-lib");
    }

    #[test]
    fn test_trust_mc_result_to_verification_result_timeout() {
        let result = TrustMcResult {
            verdict: Verdict::Timeout,
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            proof_mode: TrustMcProofMode::Bmc,
            proof_provenance: Some(TrustMcProofProvenance::bmc(100, "test")),
            time_ms: 30_000,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test_fn".to_string(),
        };
        let vr = result.to_verification_result();
        assert!(matches!(vr, trust_types::VerificationResult::Timeout { .. }));
    }

    #[test]
    fn test_trust_mc_config_builder() {
        let config = TrustMcConfig::new()
            .with_bmc_depth(200)
            .with_timeout(60_000)
            .with_solver_path("/usr/local/bin/trust-mc")
            .with_diagnostics(DiagConfig::Capture)
            .with_proofs(true)
            .with_adaptive_depth(true)
            .with_proof_mode(TrustMcProofMode::FiniteAcyclicBmc);

        assert_eq!(config.bmc_depth, 200);
        assert_eq!(config.timeout_ms, 60_000);
        assert_eq!(config.solver_path.as_deref(), Some("/usr/local/bin/trust-mc"));
        assert_eq!(config.diagnostics, DiagConfig::Capture);
        assert!(config.produce_proofs);
        assert!(config.adaptive_depth);
        assert_eq!(config.proof_mode, TrustMcProofMode::FiniteAcyclicBmc);
    }

    #[test]
    fn test_encoding_context_extracts_variables() {
        let script = "(declare-const x Int)\n(declare-const y Bool)\n(assert (= x 0))\n";
        let ctx = crate::result::EncodingContext::from_smtlib(
            "test_fn".to_string(),
            script.to_string(),
            100,
        );
        assert_eq!(ctx.variable_names, vec!["x", "y"]);
        assert_eq!(ctx.function_name, "test_fn");
        assert_eq!(ctx.bmc_depth, 100);
    }
}
