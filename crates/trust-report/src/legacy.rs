//! Legacy proof report API (backward compatibility).
//!
//! Prefer `build_json_report` for new code. These functions exist for
//! backward compatibility with existing callers that use `ProofReport`.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap; // Trust: BTreeMap for deterministic output
use std::path::Path;

use trust_types::*;

/// Group results by function and build a legacy proof report.
///
/// Prefer `build_json_report` for new code -- this function exists for
/// backward compatibility with existing callers.
pub fn build_report(
    crate_name: &str,
    results: &[(VerificationCondition, VerificationResult)],
) -> ProofReport {
    let mut by_function: BTreeMap<String, Vec<(&VerificationCondition, &VerificationResult)>> =
        BTreeMap::new();

    for (vc, result) in results {
        by_function.entry(vc.function.as_str().to_string()).or_default().push((vc, result));
    }

    let mut functions = Vec::new();
    let mut total_proved = 0;
    let mut total_failed = 0;
    let mut total_unknown = 0;

    for (func_name, pairs) in &by_function {
        let mut proved = Vec::new();
        let mut failed = Vec::new();
        let mut unknown = Vec::new();

        for (vc, result) in pairs {
            match result {
                VerificationResult::Proved { solver, time_ms, strength, .. } => {
                    proved.push(ProvedProperty {
                        description: vc.kind.description(),
                        solver: solver.to_string(),
                        time_ms: *time_ms,
                        strength: strength.clone(),
                        // Wire ProofEvidence into legacy report.
                        evidence: Some(strength.clone().into()),
                    });
                    total_proved += 1;
                }
                VerificationResult::Failed { solver, counterexample, .. } => {
                    failed.push(FailedProperty {
                        description: vc.kind.description(),
                        solver: solver.to_string(),
                        counterexample: counterexample.clone(),
                    });
                    total_failed += 1;
                }
                VerificationResult::Unknown { solver, reason, .. } => {
                    unknown.push(UnknownProperty {
                        description: vc.kind.description(),
                        solver: solver.to_string(),
                        reason: reason.clone(),
                    });
                    total_unknown += 1;
                }
                VerificationResult::Timeout { solver, timeout_ms, .. } => {
                    unknown.push(UnknownProperty {
                        description: vc.kind.description(),
                        solver: solver.to_string(),
                        reason: format!("timeout after {timeout_ms}ms"),
                    });
                    total_unknown += 1;
                }
                _ => { /* unhandled verification result variant */ }
            }
        }

        functions.push(FunctionReport { function: func_name.clone(), proved, failed, unknown });
    }

    functions.sort_by(|a, b| a.function.cmp(&b.function));

    ProofReport {
        crate_name: crate_name.to_string(),
        functions,
        total_proved,
        total_failed,
        total_unknown,
    }
}

/// Write the legacy proof report as JSON.
pub fn write_report(report: &ProofReport, output_dir: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(output_dir)?;
    let json = serde_json::to_string_pretty(report)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    std::fs::write(output_dir.join("report.json"), json)?;
    Ok(())
}

/// Format a legacy report as a human-readable summary string.
pub fn format_summary(report: &ProofReport) -> String {
    let mut lines = Vec::new();

    for func in &report.functions {
        lines.push(format!("  {}", func.function));

        for p in &func.proved {
            lines.push(format!("    {} PROVED ({}, {}ms)", p.description, p.solver, p.time_ms));
        }
        for f in &func.failed {
            let cex = f
                .counterexample
                .as_ref()
                .map(|c| format!(" counterexample: {c}"))
                .unwrap_or_default();
            lines.push(format!("    {} FAILED ({}){cex}", f.description, f.solver));
        }
        for u in &func.unknown {
            lines.push(format!("    {} UNKNOWN ({}: {})", u.description, u.solver, u.reason));
        }
    }

    lines.push(String::new());
    lines.push(format!(
        "  {} functions, {} proved, {} failed, {} unknown",
        report.functions.len(),
        report.total_proved,
        report.total_failed,
        report.total_unknown
    ));

    lines.join("\n")
}
