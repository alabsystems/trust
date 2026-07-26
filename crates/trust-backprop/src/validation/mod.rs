//! Rewrite validation for trust-backprop.
//!
//! Validates that proposed rewrites preserve behavior: syntax validity,
//! type preservation, spec strengthening, and semantic preservation via
//! structural diffing of simplified AST representations.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

mod cargo_exec;
mod checks;
mod helpers;
pub(crate) mod semantic;
mod types;

#[cfg(test)]
mod tests;

// Re-export public API.
use cargo_exec::{run_cargo_check, run_cargo_test};
use checks::{
    check_conservative_strengthening, check_formula_valid, check_no_new_warnings,
    check_specs_strengthen, check_syntax_valid, check_tests_pass_heuristic, check_type_consistency,
    check_types_preserved,
};
pub use semantic::{check_semantic_preservation, parse_simplified_ast};
pub use types::{
    AstNode, CheckResult, SemanticDiff, ValidationCheck, ValidationConfig, ValidationResult,
};

/// Validate a proposed rewrite against a set of checks.
///
/// Performs each requested check on the original vs. rewritten source and
/// returns a `ValidationResult` summarizing pass/fail for each.
///
/// When both sources are parseable by `syn`, this function uses AST-based
/// validation for `SyntaxValid` and `TypesPreserved` checks, producing more
/// robust results that are insensitive to whitespace, comments, and formatting.
/// Falls back to heuristic string matching when `syn` cannot parse the source.
#[must_use]
pub fn validate_rewrite(
    original: &str,
    rewritten: &str,
    checks: &[ValidationCheck],
) -> ValidationResult {
    let mut passed = Vec::new();
    let mut failed = Vec::new();
    let mut warnings = Vec::new();

    // Attempt AST-based validation for structural checks.
    let ast_result = crate::ast_validation::validate_rewrite_ast(original, rewritten);
    let use_ast = ast_result.used_ast;

    if !use_ast {
        warnings.push("AST parsing failed; using heuristic string-based validation".into());
    }

    for check in checks {
        let result = if use_ast {
            run_check_with_ast(original, rewritten, check, &ast_result, &mut warnings)
        } else {
            run_check(original, rewritten, check, &mut warnings)
        };
        if result.passed {
            passed.push(result);
        } else {
            failed.push(result);
        }
    }

    ValidationResult { passed_checks: passed, failed_checks: failed, warnings }
}

/// Validate a proposed rewrite with configuration for test execution.
///
/// Like [`validate_rewrite`], but when `config.crate_path` is set and
/// `TestsPass` is in `checks`, this function actually runs `cargo test`
/// on the crate to verify tests still pass after the rewrite.
///
/// Fail-closed: if `cargo test` cannot be executed, times out, or returns
/// a non-zero exit code, the `TestsPass` check fails.
#[must_use]
pub fn validate_rewrite_with_config(
    original: &str,
    rewritten: &str,
    checks: &[ValidationCheck],
    config: &ValidationConfig,
) -> ValidationResult {
    let mut passed = Vec::new();
    let mut failed = Vec::new();
    let mut warnings = Vec::new();

    let ast_result = crate::ast_validation::validate_rewrite_ast(original, rewritten);
    let use_ast = ast_result.used_ast;

    if !use_ast {
        warnings.push("AST parsing failed; using heuristic string-based validation".into());
    }

    for check in checks {
        let result = if matches!(check, ValidationCheck::TestsPass) {
            run_tests_pass_check(original, rewritten, config, &mut warnings)
        } else if matches!(check, ValidationCheck::SyntaxValid) {
            run_syntax_valid_check(rewritten, use_ast, config, &mut warnings)
        } else if use_ast {
            run_check_with_ast(original, rewritten, check, &ast_result, &mut warnings)
        } else {
            run_check(original, rewritten, check, &mut warnings)
        };
        if result.passed {
            passed.push(result);
        } else {
            failed.push(result);
        }
    }

    ValidationResult { passed_checks: passed, failed_checks: failed, warnings }
}

/// Run the `TestsPass` check with optional cargo test execution.
///
/// Strategy:
/// 1. Run the heuristic check first (cheap, catches removed test constructs).
/// 2. If the heuristic fails, return immediately (fast-path rejection).
/// 3. If `config.crate_path` is set, run `cargo test` for real validation.
/// 4. Fail-closed on any execution error.
fn run_tests_pass_check(
    original: &str,
    rewritten: &str,
    config: &ValidationConfig,
    warnings: &mut Vec<String>,
) -> CheckResult {
    // Fast-path: heuristic check catches removed test constructs cheaply.
    let heuristic = check_tests_pass_heuristic(original, rewritten, warnings);
    if !heuristic.passed {
        return heuristic;
    }

    // If no crate path configured, return the heuristic result.
    let Some(crate_path) = &config.crate_path else {
        return heuristic;
    };

    // Run actual cargo test on the crate.
    match run_cargo_test(crate_path, config.test_timeout) {
        Ok(test_result) => {
            if test_result.success {
                CheckResult {
                    check: ValidationCheck::TestsPass,
                    passed: true,
                    detail: format!(
                        "cargo test passed ({}). Heuristic: {}",
                        test_result.summary, heuristic.detail
                    ),
                }
            } else {
                CheckResult {
                    check: ValidationCheck::TestsPass,
                    passed: false,
                    detail: format!("cargo test FAILED: {}", test_result.summary),
                }
            }
        }
        Err(e) => {
            // Fail-closed: any execution error means tests did not pass.
            CheckResult {
                check: ValidationCheck::TestsPass,
                passed: false,
                detail: format!("cargo test execution error (fail-closed): {e}"),
            }
        }
    }
}

/// Run the `SyntaxValid` check with optional `cargo check` invocation.
///
/// Strategy:
/// 1. Attempt `syn::parse_file()` (or use AST result if already parsed).
/// 2. If syn fails, reject immediately.
/// 3. If syn passes and `config.compile_check_enabled` is true and
///    `config.crate_path` is set, run `cargo check` for full semantic validation.
/// 4. Fail-closed: if `cargo check` cannot be run when configured, reject.
fn run_syntax_valid_check(
    rewritten: &str,
    ast_already_parsed: bool,
    config: &ValidationConfig,
    warnings: &mut Vec<String>,
) -> CheckResult {
    // Step 1: syn-based parse check.
    let syn_ok = if ast_already_parsed { true } else { syn::parse_file(rewritten).is_ok() };

    if !syn_ok {
        return CheckResult {
            check: ValidationCheck::SyntaxValid,
            passed: false,
            detail: "syn parse error: source is not valid Rust".into(),
        };
    }

    // Step 2: If cargo check is enabled and crate_path is available, run it.
    let Some(crate_path) = &config.crate_path else {
        return CheckResult {
            check: ValidationCheck::SyntaxValid,
            passed: true,
            detail: "Parsed successfully by syn (no crate_path for cargo check)".into(),
        };
    };

    if !config.compile_check_enabled {
        return CheckResult {
            check: ValidationCheck::SyntaxValid,
            passed: true,
            detail: "Parsed successfully by syn (cargo check disabled)".into(),
        };
    }

    // Run cargo check on the crate.
    match run_cargo_check(crate_path, config.compile_check_timeout) {
        Ok(check_result) => {
            if check_result.success {
                CheckResult {
                    check: ValidationCheck::SyntaxValid,
                    passed: true,
                    detail: format!(
                        "Parsed by syn + cargo check passed ({})",
                        check_result.summary
                    ),
                }
            } else {
                CheckResult {
                    check: ValidationCheck::SyntaxValid,
                    passed: false,
                    detail: format!(
                        "syn parsed OK but cargo check FAILED: {}",
                        check_result.summary
                    ),
                }
            }
        }
        Err(e) => {
            // Fail-closed: if cargo check cannot be run, reject the rewrite.
            warnings.push(format!("cargo check execution error: {e}"));
            CheckResult {
                check: ValidationCheck::SyntaxValid,
                passed: false,
                detail: format!(
                    "syn parsed OK but cargo check failed to execute (fail-closed): {e}"
                ),
            }
        }
    }
}

/// Run a validation check using AST results for structural checks, falling
/// back to heuristic checks for non-structural ones.
fn run_check_with_ast(
    original: &str,
    rewritten: &str,
    check: &ValidationCheck,
    ast_result: &crate::ast_validation::AstValidationResult,
    warnings: &mut Vec<String>,
) -> CheckResult {
    match check {
        ValidationCheck::SyntaxValid => {
            // AST parsed successfully, so syntax is valid.
            CheckResult {
                check: ValidationCheck::SyntaxValid,
                passed: true,
                detail: "Parsed successfully by syn".into(),
            }
        }
        ValidationCheck::TypesPreserved => {
            // Use AST-based signature comparison.
            let sig_errors: Vec<_> = ast_result
                .errors
                .iter()
                .filter(|e| {
                    matches!(
                        e,
                        crate::ast_validation::AstValidationError::SignatureChanged { .. }
                            | crate::ast_validation::AstValidationError::FunctionRemoved { .. }
                            | crate::ast_validation::AstValidationError::FunctionAdded { .. }
                            | crate::ast_validation::AstValidationError::NonBodyModification { .. }
                    )
                })
                .collect();

            if sig_errors.is_empty() {
                CheckResult {
                    check: ValidationCheck::TypesPreserved,
                    passed: true,
                    detail: "AST-based: all function signatures preserved".into(),
                }
            } else {
                let details: Vec<String> = sig_errors.iter().map(|e| e.to_string()).collect();
                CheckResult {
                    check: ValidationCheck::TypesPreserved,
                    passed: false,
                    detail: format!("AST-based: {}", details.join("; ")),
                }
            }
        }
        // For checks without AST-based equivalents, fall back to heuristics.
        _ => run_check(original, rewritten, check, warnings),
    }
}

/// Run a single validation check.
fn run_check(
    original: &str,
    rewritten: &str,
    check: &ValidationCheck,
    warnings: &mut Vec<String>,
) -> CheckResult {
    match check {
        ValidationCheck::SyntaxValid => check_syntax_valid(rewritten),
        ValidationCheck::TypesPreserved => check_types_preserved(original, rewritten),
        ValidationCheck::TestsPass => check_tests_pass_heuristic(original, rewritten, warnings),
        ValidationCheck::SpecsStrengthen => check_specs_strengthen(original, rewritten),
        ValidationCheck::NoNewWarnings => check_no_new_warnings(original, rewritten),
        ValidationCheck::FormulaValid => check_formula_valid(rewritten),
        ValidationCheck::TypeConsistency => check_type_consistency(rewritten),
        ValidationCheck::ConservativeStrengthening => {
            check_conservative_strengthening(original, rewritten)
        }
    }
}
