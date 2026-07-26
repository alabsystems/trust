//! Individual validation check implementations.
//!
//! Each function performs one specific validation check on source code,
//! returning a `CheckResult` with pass/fail and detail.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::parse_spec_expr_result;

use super::helpers::{
    count_occurrences, count_warning_patterns, extract_all_param_names, extract_fn_signatures,
    extract_identifiers, extract_spec_attributes, extract_spec_body, is_type_constant,
    strip_spec_lines,
};
use super::types::{CheckResult, ValidationCheck};
use trust_types::fx::FxHashSet;

/// Check that the rewritten source is syntactically valid Rust.
pub(crate) fn check_syntax_valid(rewritten: &str) -> CheckResult {
    // Use syn-based parsing -- this catches real syntax errors.
    let rewritten = match crate::ast_rewriter::mask_native_contract_clauses(rewritten) {
        Ok(source) => source,
        Err(error) => {
            return CheckResult {
                check: ValidationCheck::SyntaxValid,
                passed: false,
                detail: error.to_string(),
            };
        }
    };
    match syn::parse_file(&rewritten) {
        Ok(_) => CheckResult {
            check: ValidationCheck::SyntaxValid,
            passed: true,
            detail: "Parsed successfully by syn".into(),
        },
        Err(e) => CheckResult {
            check: ValidationCheck::SyntaxValid,
            passed: false,
            detail: format!("syn parse error: {e}"),
        },
    }
}

/// Check that the function signature is preserved between original and rewritten.
///
/// Extracts `fn` signatures and compares them, ignoring spec attributes.
pub(crate) fn check_types_preserved(original: &str, rewritten: &str) -> CheckResult {
    let orig_sigs = extract_fn_signatures(original);
    let new_sigs = extract_fn_signatures(rewritten);

    if orig_sigs == new_sigs {
        CheckResult {
            check: ValidationCheck::TypesPreserved,
            passed: true,
            detail: format!("All {} function signature(s) preserved", orig_sigs.len()),
        }
    } else {
        let orig_set: FxHashSet<_> = orig_sigs.iter().collect();
        let new_set: FxHashSet<_> = new_sigs.iter().collect();
        let changed: Vec<_> = orig_set.symmetric_difference(&new_set).collect();
        CheckResult {
            check: ValidationCheck::TypesPreserved,
            passed: false,
            detail: format!(
                "Function signature(s) changed: {}",
                changed.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
            ),
        }
    }
}

/// Heuristic check that the rewrite does not remove test code.
///
/// Fail-closed: if the original contains test constructs and any are removed
/// in the rewrite, the check fails. We compare counts of `#[test]`,
/// `#[cfg(test)]`, and `fn test_` between original and rewritten source.
// Trust: security fix - was always returning true
pub(crate) fn check_tests_pass_heuristic(
    original: &str,
    rewritten: &str,
    warnings: &mut Vec<String>,
) -> CheckResult {
    let orig_test_attrs = count_occurrences(original, "#[test]");
    let new_test_attrs = count_occurrences(rewritten, "#[test]");
    let orig_cfg_test = count_occurrences(original, "#[cfg(test)]");
    let new_cfg_test = count_occurrences(rewritten, "#[cfg(test)]");
    let orig_test_fns = count_occurrences(original, "fn test_");
    let new_test_fns = count_occurrences(rewritten, "fn test_");

    // Detect removed test constructs
    let mut removals = Vec::new();
    if new_test_attrs < orig_test_attrs {
        removals.push(format!(
            "#[test] attributes reduced from {} to {}",
            orig_test_attrs, new_test_attrs
        ));
    }
    if new_cfg_test < orig_cfg_test {
        removals.push(format!(
            "#[cfg(test)] modules reduced from {} to {}",
            orig_cfg_test, new_cfg_test
        ));
    }
    if new_test_fns < orig_test_fns {
        removals.push(format!(
            "test functions (fn test_) reduced from {} to {}",
            orig_test_fns, new_test_fns
        ));
    }

    // Warn if rewritten has test fn names but missing #[test] attribute
    if new_test_attrs == 0 && rewritten.contains("fn test_") {
        warnings.push("Test functions found without #[test] attribute".into());
    }

    if !removals.is_empty() {
        // Fail-closed: test code was removed
        CheckResult {
            check: ValidationCheck::TestsPass,
            passed: false,
            detail: format!("Test code removed: {}", removals.join("; ")),
        }
    } else if orig_test_attrs == 0 && orig_cfg_test == 0 && orig_test_fns == 0 {
        // No test constructs in either version -- nothing to validate
        CheckResult {
            check: ValidationCheck::TestsPass,
            passed: true,
            detail: "No test constructs in original or rewrite".into(),
        }
    } else {
        // Test constructs preserved (or added)
        CheckResult {
            check: ValidationCheck::TestsPass,
            passed: true,
            detail: format!(
                "Test constructs preserved: {} #[test], {} #[cfg(test)], {} fn test_",
                new_test_attrs, new_cfg_test, new_test_fns
            ),
        }
    }
}

/// Check that specs are only strengthened (added), never weakened (removed).
pub(crate) fn check_specs_strengthen(original: &str, rewritten: &str) -> CheckResult {
    let orig_specs = extract_spec_attributes(original);
    let new_specs = extract_spec_attributes(rewritten);

    // All original specs must still be present, including duplicate clauses.
    let mut remaining = std::collections::BTreeMap::<&str, usize>::new();
    for spec in &new_specs {
        *remaining.entry(spec.as_str()).or_default() += 1;
    }
    let mut removed = Vec::new();
    for spec in &orig_specs {
        let count = remaining.entry(spec.as_str()).or_default();
        if *count == 0 {
            removed.push(spec.clone());
        } else {
            *count -= 1;
        }
    }

    if removed.is_empty() {
        let added_count = new_specs.len().saturating_sub(orig_specs.len());
        CheckResult {
            check: ValidationCheck::SpecsStrengthen,
            passed: true,
            detail: format!(
                "Specs preserved ({} existing) + {} added",
                orig_specs.len(),
                added_count
            ),
        }
    } else {
        CheckResult {
            check: ValidationCheck::SpecsStrengthen,
            passed: false,
            detail: format!("Specs removed (weakened): {}", removed.join(", ")),
        }
    }
}

/// Heuristic check for new warnings by looking for common warning patterns.
pub(crate) fn check_no_new_warnings(original: &str, rewritten: &str) -> CheckResult {
    let orig_warnings = count_warning_patterns(original);
    let new_warnings = count_warning_patterns(rewritten);

    if new_warnings <= orig_warnings {
        CheckResult {
            check: ValidationCheck::NoNewWarnings,
            passed: true,
            detail: format!("Warning patterns: {orig_warnings} -> {new_warnings}"),
        }
    } else {
        CheckResult {
            check: ValidationCheck::NoNewWarnings,
            passed: false,
            detail: format!("New warning patterns detected: {orig_warnings} -> {new_warnings}"),
        }
    }
}

/// Check that all spec formula bodies in the rewritten source parse via trust-types.
///
/// Extracts native/compatibility clause bodies and parses each as a `Formula`.
pub(crate) fn check_formula_valid(rewritten: &str) -> CheckResult {
    let specs = extract_spec_attributes(rewritten);
    if specs.is_empty() {
        return CheckResult {
            check: ValidationCheck::FormulaValid,
            passed: true,
            detail: "No contract clauses to validate".into(),
        };
    }

    let mut failures: Vec<String> = Vec::new();
    let mut valid_count = 0usize;

    for spec_line in &specs {
        if let Some(body) = extract_spec_body(spec_line) {
            match parse_spec_expr_result(&body) {
                Ok(_) => valid_count += 1,
                Err(e) => failures.push(format!("{body}: {e}")),
            }
        }
    }

    if failures.is_empty() {
        CheckResult {
            check: ValidationCheck::FormulaValid,
            passed: true,
            detail: format!("All {valid_count} spec formula(s) parse successfully"),
        }
    } else {
        CheckResult {
            check: ValidationCheck::FormulaValid,
            passed: false,
            detail: format!(
                "{} formula(s) failed to parse: {}",
                failures.len(),
                failures.join("; ")
            ),
        }
    }
}

/// Check that inserted specs only reference identifiers from the function signature.
///
/// Extracts parameter names from `fn` signatures and checks that new contract clauses
/// only reference those identifiers (plus native output names and literals).
pub(crate) fn check_type_consistency(rewritten: &str) -> CheckResult {
    let param_names = extract_all_param_names(rewritten);
    let specs = extract_spec_attributes(rewritten);

    if specs.is_empty() {
        return CheckResult {
            check: ValidationCheck::TypeConsistency,
            passed: true,
            detail: "No contract clauses to check".into(),
        };
    }

    // Allowed identifiers: function params + special names
    let mut allowed: FxHashSet<&str> = param_names.iter().map(|s| s.as_str()).collect();
    allowed.insert("result");
    allowed.insert("true");
    allowed.insert("false");
    allowed.insert("out");
    allowed.insert("forall");
    allowed.insert("exists");

    let mut unknown: Vec<String> = Vec::new();

    for spec_line in &specs {
        if let Some(body) = extract_spec_body(spec_line) {
            for ident in extract_identifiers(&body) {
                if !allowed.contains(ident.as_str()) && !is_type_constant(&ident) {
                    unknown.push(ident);
                }
            }
        }
    }

    // Deduplicate
    unknown.sort();
    unknown.dedup();

    if unknown.is_empty() {
        CheckResult {
            check: ValidationCheck::TypeConsistency,
            passed: true,
            detail: format!("All spec identifiers reference known parameters: {:?}", param_names),
        }
    } else {
        CheckResult {
            check: ValidationCheck::TypeConsistency,
            passed: false,
            detail: format!("Spec references unknown identifiers: {}", unknown.join(", ")),
        }
    }
}

/// Check that the rewrite is conservative: non-spec code is unchanged.
///
/// Compares original and rewritten source after stripping contract clauses and
/// assertions. Only additive spec changes are allowed.
pub(crate) fn check_conservative_strengthening(original: &str, rewritten: &str) -> CheckResult {
    let orig_stripped = strip_spec_lines(original);
    let new_stripped = strip_spec_lines(rewritten);

    if orig_stripped == new_stripped {
        // Count how many spec lines were added
        let orig_specs = extract_spec_attributes(original).len();
        let new_specs = extract_spec_attributes(rewritten).len();
        let added = new_specs.saturating_sub(orig_specs);

        CheckResult {
            check: ValidationCheck::ConservativeStrengthening,
            passed: true,
            detail: format!(
                "Non-spec code unchanged; {added} spec(s) added, {orig_specs} preserved"
            ),
        }
    } else {
        CheckResult {
            check: ValidationCheck::ConservativeStrengthening,
            passed: false,
            detail: "Non-spec code was modified by the rewrite".into(),
        }
    }
}
