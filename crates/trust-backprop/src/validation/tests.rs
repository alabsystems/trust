//! Tests for rewrite validation.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use super::cargo_exec::{
    TrustCargoCommand, TrustCargoSearch, build_targo_command, extract_test_summary,
    is_validation_env_denied, resolve_targo, run_cargo_check, run_cargo_test,
    run_command_with_timeout,
};
use super::checks::*;
use super::helpers::{
    extract_identifiers, extract_spec_attributes, extract_spec_body, is_type_constant,
    strip_spec_lines,
};
use super::semantic::{extract_fn_name, extract_fn_params, extract_return_type};
use super::types::*;
use super::{
    check_semantic_preservation, parse_simplified_ast, validate_rewrite,
    validate_rewrite_with_config,
};

// --- validate_rewrite tests ---

#[test]
fn test_validate_rewrite_all_pass() {
    let original = "fn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let rewritten = "#[requires(\"x < u64::MAX\")]\nfn foo(x: u64) -> u64 {\n    x + 1\n}\n";

    let result = validate_rewrite(
        original,
        rewritten,
        &[
            ValidationCheck::SyntaxValid,
            ValidationCheck::TypesPreserved,
            ValidationCheck::SpecsStrengthen,
        ],
    );

    assert!(result.is_valid());
    assert_eq!(result.total_checks(), 3);
    assert_eq!(result.passed_checks.len(), 3);
    assert!(result.failed_checks.is_empty());
}

#[test]
fn test_validate_rewrite_syntax_invalid() {
    let original = "fn foo() {}\n";
    let rewritten = "fn foo() {\n"; // missing closing brace

    let result = validate_rewrite(original, rewritten, &[ValidationCheck::SyntaxValid]);

    assert!(!result.is_valid());
    assert_eq!(result.failed_checks.len(), 1);
    assert_eq!(result.failed_checks[0].check, ValidationCheck::SyntaxValid);
}

#[test]
fn test_validate_rewrite_signature_changed() {
    let original = "fn foo(x: u64) -> u64 {\n    x\n}\n";
    let rewritten = "fn foo(x: i64) -> i64 {\n    x\n}\n";

    let result = validate_rewrite(original, rewritten, &[ValidationCheck::TypesPreserved]);

    assert!(!result.is_valid());
    assert_eq!(result.failed_checks[0].check, ValidationCheck::TypesPreserved);
}

#[test]
fn test_validate_rewrite_spec_removed() {
    let original = "#[requires(\"x > 0\")]\nfn foo(x: u64) {}\n";
    let rewritten = "fn foo(x: u64) {}\n";

    let result = validate_rewrite(original, rewritten, &[ValidationCheck::SpecsStrengthen]);

    assert!(!result.is_valid());
    assert_eq!(result.failed_checks[0].check, ValidationCheck::SpecsStrengthen);
}

#[test]
fn test_validate_rewrite_spec_added() {
    let original = "fn foo(x: u64) {}\n";
    let rewritten = "#[requires(\"x > 0\")]\nfn foo(x: u64) {}\n";

    let result = validate_rewrite(original, rewritten, &[ValidationCheck::SpecsStrengthen]);

    assert!(result.is_valid());
    assert!(result.passed_checks[0].detail.contains("1 added"));
}

#[test]
fn test_validate_rewrite_no_checks() {
    let result = validate_rewrite("fn a() {}", "fn b() {}", &[]);
    assert!(result.is_valid());
    assert_eq!(result.total_checks(), 0);
}

// --- SyntaxValid tests ---

#[test]
fn test_syntax_balanced_braces() {
    let result = check_syntax_valid("fn foo() { if true { bar() } }");
    assert!(result.passed);
}

#[test]
fn test_syntax_unbalanced_open_brace() {
    let result = check_syntax_valid("fn foo() {");
    assert!(!result.passed);
    assert!(result.detail.contains("syn parse error"), "detail: {}", result.detail);
}

#[test]
fn test_syntax_unbalanced_close_brace() {
    let result = check_syntax_valid("fn foo() }");
    assert!(!result.passed);
    assert!(result.detail.contains("syn parse error"), "detail: {}", result.detail);
}

#[test]
fn test_syntax_balanced_parens_and_brackets() {
    let result = check_syntax_valid("fn foo(x: Vec<[u8; 4]>) -> (u64, u64) {}");
    assert!(result.passed);
}

#[test]
fn test_syntax_ignores_braces_in_strings() {
    let result = check_syntax_valid("fn foo() { let s = \"{\"; }");
    assert!(result.passed);
}

#[test]
fn test_syntax_ignores_braces_in_comments() {
    let result = check_syntax_valid("fn foo() {\n// this { is a comment\n}");
    assert!(result.passed);
}

// --- TypesPreserved tests ---

#[test]
fn test_types_preserved_identical() {
    let source = "fn foo(x: u64) -> u64 {\n    x\n}\n";
    let result = check_types_preserved(source, source);
    assert!(result.passed);
}

#[test]
fn test_types_preserved_with_added_attr() {
    let original = "fn foo(x: u64) -> u64 {\n    x\n}\n";
    let rewritten = "#[requires(\"x > 0\")]\nfn foo(x: u64) -> u64 {\n    x\n}\n";
    let result = check_types_preserved(original, rewritten);
    assert!(result.passed);
}

#[test]
fn test_types_changed_param() {
    let original = "fn foo(x: u64) -> u64 {\n    x\n}\n";
    let rewritten = "fn foo(x: u32) -> u64 {\n    x as u64\n}\n";
    let result = check_types_preserved(original, rewritten);
    assert!(!result.passed);
}

#[test]
fn test_types_changed_return() {
    let original = "fn foo(x: u64) -> u64 {\n    x\n}\n";
    let rewritten = "fn foo(x: u64) -> Option<u64> {\n    Some(x)\n}\n";
    let result = check_types_preserved(original, rewritten);
    assert!(!result.passed);
}

// --- SpecsStrengthen tests ---

#[test]
fn test_specs_strengthen_adding_spec() {
    let original = "fn foo() {}";
    let rewritten = "#[requires(\"true\")]\nfn foo() {}";
    let result = check_specs_strengthen(original, rewritten);
    assert!(result.passed);
}

#[test]
fn test_specs_strengthen_keeping_spec() {
    let original = "#[requires(\"x > 0\")]\nfn foo() {}";
    let rewritten = "#[requires(\"x > 0\")]\n#[ensures(\"result > 0\")]\nfn foo() {}";
    let result = check_specs_strengthen(original, rewritten);
    assert!(result.passed);
}

#[test]
fn test_specs_weaken_removing_spec() {
    let original = "#[requires(\"x > 0\")]\nfn foo() {}";
    let rewritten = "fn foo() {}";
    let result = check_specs_strengthen(original, rewritten);
    assert!(!result.passed);
    assert!(result.detail.contains("removed"));
}

// --- NoNewWarnings tests ---

#[test]
fn test_no_new_warnings_clean() {
    let original = "fn foo() { let x = 1; }";
    let rewritten = "fn foo() { let x = 1; }";
    let result = check_no_new_warnings(original, rewritten);
    assert!(result.passed);
}

#[test]
fn test_no_new_warnings_added_allow() {
    let original = "fn foo() {}";
    let rewritten = "#[allow(unused)]\nfn foo() {}";
    let result = check_no_new_warnings(original, rewritten);
    assert!(!result.passed);
}

#[test]
fn test_no_new_warnings_existing_allow() {
    let original = "#[allow(unused)]\nfn foo() {}";
    let rewritten = "#[allow(unused)]\nfn foo() {}";
    let result = check_no_new_warnings(original, rewritten);
    assert!(result.passed);
}

// --- Semantic preservation tests ---

#[test]
fn test_semantic_preservation_no_change() {
    let source = "fn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let diff = check_semantic_preservation(source, source);
    assert!(diff.preserves_semantics);
    assert!(diff.added.is_empty());
    assert!(diff.removed.is_empty());
    assert!(diff.summary.contains("No structural changes"));
}

#[test]
fn test_semantic_preservation_added_attribute() {
    let original = "fn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let rewritten = "#[requires(\"x < u64::MAX\")]\nfn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let diff = check_semantic_preservation(original, rewritten);
    assert!(diff.preserves_semantics);
    assert_eq!(diff.added.len(), 1);
    assert!(matches!(&diff.added[0], AstNode::Attribute { .. }));
    assert!(diff.removed.is_empty());
}

#[test]
fn test_semantic_preservation_removed_statement() {
    let original = "fn foo() {\n    let x = 1;\n    let y = 2;\n}\n";
    let rewritten = "fn foo() {\n    let x = 1;\n}\n";
    let diff = check_semantic_preservation(original, rewritten);
    assert!(!diff.preserves_semantics);
    assert!(!diff.removed.is_empty());
}

#[test]
fn test_semantic_preservation_changed_body() {
    let original = "fn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let rewritten = "fn foo(x: u64) -> u64 {\n    x.checked_add(1).unwrap()\n}\n";
    let diff = check_semantic_preservation(original, rewritten);
    // Body changed: statement differs
    assert!(!diff.preserves_semantics);
}

// --- AST parsing tests ---

#[test]
fn test_parse_function() {
    let source = "fn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let ast = parse_simplified_ast(source);
    assert_eq!(ast.len(), 1);
    assert!(matches!(&ast[0], AstNode::Function { name, .. } if name == "foo"));
}

#[test]
fn test_parse_attribute_then_function() {
    let source = "#[requires(\"x > 0\")]\nfn foo(x: u64) {\n}\n";
    let ast = parse_simplified_ast(source);
    assert_eq!(ast.len(), 2);
    assert!(matches!(&ast[0], AstNode::Attribute { text } if text.contains("requires")));
    assert!(matches!(&ast[1], AstNode::Function { name, .. } if name == "foo"));
}

#[test]
fn test_parse_return_node() {
    let ast = parse_simplified_ast("return 42;");
    assert_eq!(ast.len(), 1);
    assert!(matches!(&ast[0], AstNode::Return { expr: Some(e) } if e == "42"));
}

#[test]
fn test_parse_bare_return() {
    let ast = parse_simplified_ast("return;");
    assert_eq!(ast.len(), 1);
    assert!(matches!(&ast[0], AstNode::Return { expr: None }));
}

#[test]
fn test_extract_fn_name_simple() {
    assert_eq!(extract_fn_name("fn foo() {"), Some("foo".into()));
    assert_eq!(extract_fn_name("pub fn bar(x: u64) -> u64 {"), Some("bar".into()));
}

#[test]
fn test_extract_fn_params_multiple() {
    let params = extract_fn_params("fn foo(a: u64, b: u64) -> u64 {");
    assert_eq!(params, vec!["a: u64", "b: u64"]);
}

#[test]
fn test_extract_fn_params_empty() {
    let params = extract_fn_params("fn foo() {");
    assert!(params.is_empty());
}

#[test]
fn test_extract_return_type_present() {
    assert_eq!(extract_return_type("fn foo(x: u64) -> u64 {"), Some("u64".into()));
}

#[test]
fn test_extract_return_type_absent() {
    assert_eq!(extract_return_type("fn foo() {"), None);
}

// --- ValidationResult tests ---

#[test]
fn test_validation_result_is_valid() {
    let result = ValidationResult {
        passed_checks: vec![CheckResult {
            check: ValidationCheck::SyntaxValid,
            passed: true,
            detail: "ok".into(),
        }],
        failed_checks: vec![],
        warnings: vec![],
    };
    assert!(result.is_valid());
    assert_eq!(result.total_checks(), 1);
}

#[test]
fn test_validation_result_not_valid() {
    let result = ValidationResult {
        passed_checks: vec![],
        failed_checks: vec![CheckResult {
            check: ValidationCheck::SyntaxValid,
            passed: false,
            detail: "bad".into(),
        }],
        warnings: vec![],
    };
    assert!(!result.is_valid());
}

// --- Serialization tests ---

#[test]
fn test_validation_check_serialization() {
    let check = ValidationCheck::TypesPreserved;
    let json = serde_json::to_string(&check).unwrap();
    let restored: ValidationCheck = serde_json::from_str(&json).unwrap();
    assert_eq!(check, restored);
}

#[test]
fn test_semantic_diff_serialization() {
    let diff = SemanticDiff {
        added: vec![AstNode::Attribute { text: "#[requires(\"x > 0\")]".into() }],
        removed: vec![],
        preserves_semantics: true,
        summary: "1 added".into(),
    };
    let json = serde_json::to_string(&diff).unwrap();
    let restored: SemanticDiff = serde_json::from_str(&json).unwrap();
    assert!(restored.preserves_semantics);
    assert_eq!(restored.added.len(), 1);
}

// --- Integration test ---

#[test]
fn test_full_validation_workflow() {
    let original =
        concat!("pub fn get_midpoint(a: u64, b: u64) -> u64 {\n", "    (a + b) / 2\n", "}\n",);
    let rewritten = concat!(
        "#[requires(\"a + b < u64::MAX\")]\n",
        "pub fn get_midpoint(a: u64, b: u64) -> u64 {\n",
        "    (a + b) / 2\n",
        "}\n",
    );

    // Validation
    let result = validate_rewrite(
        original,
        rewritten,
        &[
            ValidationCheck::SyntaxValid,
            ValidationCheck::TypesPreserved,
            ValidationCheck::SpecsStrengthen,
            ValidationCheck::NoNewWarnings,
            ValidationCheck::TestsPass,
        ],
    );
    assert!(result.is_valid());
    assert_eq!(result.total_checks(), 5);

    // Semantic preservation
    let diff = check_semantic_preservation(original, rewritten);
    assert!(diff.preserves_semantics);
    assert_eq!(diff.added.len(), 1);
    assert!(diff.removed.is_empty());
}

// --- FormulaValid tests ---

#[test]
fn test_formula_valid_simple_comparison() {
    let source = "#[requires(\"x > 0\")]\nfn foo(x: u64) {}\n";
    let result = check_formula_valid(source);
    assert!(result.passed, "detail: {}", result.detail);
}

#[test]
fn test_formula_valid_complex_expression() {
    let source = "#[requires(\"a + b < 100\")]\n#[ensures(\"result >= 0\")]\nfn bar(a: u64, b: u64) -> u64 {}\n";
    let result = check_formula_valid(source);
    assert!(result.passed, "detail: {}", result.detail);
}

#[test]
fn test_formula_valid_no_specs() {
    let source = "fn foo() {}\n";
    let result = check_formula_valid(source);
    assert!(result.passed);
    assert!(result.detail.contains("No contract clauses"));
}

#[test]
fn test_formula_valid_malformed_body() {
    let source = "#[requires(\">>> invalid <<<\")]\nfn foo() {}\n";
    let result = check_formula_valid(source);
    assert!(!result.passed, "should fail for invalid formula");
}

#[test]
fn test_formula_valid_mixed_valid_invalid() {
    let source = "#[requires(\"x > 0\")]\n#[ensures(\"??? bad\")]\nfn foo(x: u64) {}\n";
    let result = check_formula_valid(source);
    assert!(!result.passed);
    assert!(result.detail.contains("1 formula(s) failed"));
}

// --- TypeConsistency tests ---

#[test]
fn test_type_consistency_valid_params() {
    let source = "#[requires(\"a > 0\")]\nfn foo(a: u64, b: u64) {}\n";
    let result = check_type_consistency(source);
    assert!(result.passed, "detail: {}", result.detail);
}

#[test]
fn test_type_consistency_result_allowed() {
    let source = "#[ensures(\"result > 0\")]\nfn foo(x: u64) -> u64 { x }\n";
    let result = check_type_consistency(source);
    assert!(result.passed, "detail: {}", result.detail);
}

#[test]
fn test_type_consistency_unknown_ident() {
    let source = "#[requires(\"z > 0\")]\nfn foo(x: u64) {}\n";
    let result = check_type_consistency(source);
    assert!(!result.passed);
    assert!(result.detail.contains("z"));
}

#[test]
fn test_type_consistency_type_constants_allowed() {
    let source = "#[requires(\"a < u64\")]\nfn foo(a: u64) {}\n";
    let result = check_type_consistency(source);
    // u64 is a recognized type constant
    assert!(result.passed, "detail: {}", result.detail);
}

#[test]
fn test_type_consistency_no_specs() {
    let source = "fn foo(x: u64) {}\n";
    let result = check_type_consistency(source);
    assert!(result.passed);
}

// --- ConservativeStrengthening tests ---

#[test]
fn test_conservative_only_specs_added() {
    let original = "fn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let rewritten = "#[requires(\"x < u64::MAX\")]\nfn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let result = check_conservative_strengthening(original, rewritten);
    assert!(result.passed, "detail: {}", result.detail);
}

#[test]
fn test_conservative_body_modified_fails() {
    let original = "fn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let rewritten = "fn foo(x: u64) -> u64 {\n    x.checked_add(1).unwrap()\n}\n";
    let result = check_conservative_strengthening(original, rewritten);
    assert!(!result.passed);
    assert!(result.detail.contains("modified"));
}

#[test]
fn test_conservative_identical_passes() {
    let source = "fn foo() {}\n";
    let result = check_conservative_strengthening(source, source);
    assert!(result.passed);
}

#[test]
fn test_conservative_assertion_added_passes() {
    let original = "fn foo(x: u64) {\n    do_stuff(x);\n}\n";
    let rewritten = "assert!(x > 0);\nfn foo(x: u64) {\n    do_stuff(x);\n}\n";
    let result = check_conservative_strengthening(original, rewritten);
    // assert! lines are stripped, so non-spec code is unchanged
    assert!(result.passed, "detail: {}", result.detail);
}

// --- extract_spec_body tests ---

#[test]
fn test_extract_spec_body_requires() {
    let body = extract_spec_body("#[requires(\"x > 0\")]");
    assert_eq!(body.as_deref(), Some("x > 0"));
}

#[test]
fn test_extract_spec_body_ensures() {
    let body = extract_spec_body("#[ensures(\"result >= 0\")]");
    assert_eq!(body.as_deref(), Some("result >= 0"));
}

#[test]
fn test_extract_spec_body_no_quotes() {
    // Edge case: no quotes around body
    let body = extract_spec_body("#[requires(x > 0)]");
    assert_eq!(body.as_deref(), Some("x > 0"));
}

#[test]
fn test_extract_spec_attributes_namespaced() {
    let source = "#[trust::requires(\"x > 0\")]\n#[trust::ensures(\"result >= 0\")]\nfn foo(x: u64) -> u64 { x }\n";
    let attrs = extract_spec_attributes(source);
    assert_eq!(attrs.len(), 2);
    assert!(attrs.iter().any(|attr| attr.starts_with("#[trust::requires")));
    assert!(attrs.iter().any(|attr| attr.starts_with("#[trust::ensures")));
}

#[test]
fn extract_and_validate_native_signature_clauses() {
    let source = "fn bounded(x: i32) -> i32\n    requires x >= 0\n    ensures result >= x\n{ x }\n";
    let specs = extract_spec_attributes(source);
    assert!(specs.contains(&"requires x >= 0".to_string()));
    assert!(specs.contains(&"ensures result >= x".to_string()));
    assert!(check_formula_valid(source).passed);
}

#[test]
fn duplicate_native_clause_removal_is_detected() {
    let original = "fn bounded(x: i32) -> i32\n    requires x >= 0\n    requires x >= 0\n{ x }\n";
    let rewritten = "fn bounded(x: i32) -> i32\n    requires x >= 0\n{ x }\n";
    assert!(!check_specs_strengthen(original, rewritten).passed);
}

// --- extract_identifiers tests ---

#[test]
fn test_extract_identifiers_simple() {
    let idents = extract_identifiers("a + b < MAX");
    assert!(idents.contains(&"a".to_string()));
    assert!(idents.contains(&"b".to_string()));
    assert!(idents.contains(&"MAX".to_string()));
}

#[test]
fn test_extract_identifiers_skips_numbers() {
    let idents = extract_identifiers("x > 42");
    assert!(idents.contains(&"x".to_string()));
    assert!(!idents.iter().any(|i| i == "42"));
}

// --- strip_spec_lines tests ---

#[test]
fn test_strip_spec_lines_removes_specs() {
    let source = "#[requires(\"x > 0\")]\nfn foo(x: u64) {}\n";
    let stripped = strip_spec_lines(source);
    assert!(!stripped.contains("requires"));
    assert!(stripped.contains("fn foo"));
}

#[test]
fn strip_spec_lines_removes_native_multiline_clauses_without_changing_program_tokens() {
    let original = "fn bounded(x: i32) -> i32 { x }\n";
    let rewritten = "fn bounded(x: i32) -> i32\n    requires x >= 0 &&\n        x < 100\n{ x }\n";
    assert_eq!(strip_spec_lines(original), strip_spec_lines(rewritten));
}

#[test]
fn test_strip_spec_lines_removes_assertions() {
    let source = "assert!(x > 0);\nlet y = x + 1;\n";
    let stripped = strip_spec_lines(source);
    assert!(!stripped.contains("assert!"));
    assert!(stripped.contains("let y"));
}

#[test]
fn test_strip_spec_lines_removes_namespaced_specs() {
    let source = "#[trust::requires(\"x > 0\")]\nfn foo(x: u64) {}\n";
    let stripped = strip_spec_lines(source);
    assert!(!stripped.contains("trust::requires"));
    assert!(stripped.contains("fn foo"));
}

// --- is_type_constant tests ---

#[test]
fn test_is_type_constant_known_types() {
    assert!(is_type_constant("u64"));
    assert!(is_type_constant("MAX"));
    assert!(is_type_constant("i32"));
    assert!(is_type_constant("bool"));
}

#[test]
fn test_is_type_constant_unknown() {
    assert!(!is_type_constant("my_var"));
    assert!(!is_type_constant("unknown"));
}

// --- Full workflow with new checks ---

#[test]
fn test_full_validation_with_all_checks() {
    let original = "pub fn compute(a: u64, b: u64) -> u64 {\n    a + b\n}\n";
    let rewritten =
        "#[requires(\"a + b > 0\")]\npub fn compute(a: u64, b: u64) -> u64 {\n    a + b\n}\n";

    let result = validate_rewrite(
        original,
        rewritten,
        &[
            ValidationCheck::SyntaxValid,
            ValidationCheck::TypesPreserved,
            ValidationCheck::SpecsStrengthen,
            ValidationCheck::FormulaValid,
            ValidationCheck::TypeConsistency,
            ValidationCheck::ConservativeStrengthening,
        ],
    );
    assert!(result.is_valid(), "failed checks: {:?}", result.failed_checks);
    assert_eq!(result.total_checks(), 6);
}

#[test]
fn test_full_validation_with_namespaced_specs() {
    let original = "pub fn compute(a: u64, b: u64) -> u64 {\n    a + b\n}\n";
    let rewritten = "#[trust::requires(\"a + b > 0\")]\n#[trust::ensures(\"result > a\")]\npub fn compute(a: u64, b: u64) -> u64 {\n    a + b\n}\n";

    let result = validate_rewrite(
        original,
        rewritten,
        &[
            ValidationCheck::SpecsStrengthen,
            ValidationCheck::FormulaValid,
            ValidationCheck::TypeConsistency,
            ValidationCheck::ConservativeStrengthening,
        ],
    );
    assert!(result.is_valid(), "failed checks: {:?}", result.failed_checks);
    assert_eq!(result.total_checks(), 4);
}

// --- New ValidationCheck serialization ---

#[test]
fn test_new_validation_checks_serialize() {
    for check in &[
        ValidationCheck::FormulaValid,
        ValidationCheck::TypeConsistency,
        ValidationCheck::ConservativeStrengthening,
    ] {
        let json = serde_json::to_string(check).unwrap();
        let restored: ValidationCheck = serde_json::from_str(&json).unwrap();
        assert_eq!(check, &restored);
    }
}

// --- TestsPass heuristic tests (security fix #691) ---

#[test]
fn test_tests_pass_no_test_constructs() {
    let original = "fn foo() { 1 + 1 }\n";
    let rewritten = "fn foo() { 2 }\n";
    let mut warnings = Vec::new();
    let result = check_tests_pass_heuristic(original, rewritten, &mut warnings);
    assert!(result.passed, "should pass when no test constructs: {}", result.detail);
}

#[test]
fn test_tests_pass_test_preserved() {
    let original = "#[test]\nfn test_foo() { assert!(true); }\n";
    let rewritten = "#[test]\nfn test_foo() { assert_eq!(1, 1); }\n";
    let mut warnings = Vec::new();
    let result = check_tests_pass_heuristic(original, rewritten, &mut warnings);
    assert!(result.passed, "should pass when tests preserved: {}", result.detail);
}

#[test]
fn test_tests_pass_test_removed_fails() {
    let original = "#[test]\nfn test_foo() { assert!(true); }\n#[test]\nfn test_bar() {}\n";
    let rewritten = "#[test]\nfn test_foo() { assert!(true); }\n";
    let mut warnings = Vec::new();
    let result = check_tests_pass_heuristic(original, rewritten, &mut warnings);
    assert!(!result.passed, "should FAIL when #[test] removed: {}", result.detail);
    assert!(result.detail.contains("reduced from 2 to 1"), "detail: {}", result.detail);
}

#[test]
fn test_tests_pass_all_tests_removed_fails() {
    let original = "#[test]\nfn test_foo() {}\n#[cfg(test)]\nmod tests {}\n";
    let rewritten = "fn foo() {}\n";
    let mut warnings = Vec::new();
    let result = check_tests_pass_heuristic(original, rewritten, &mut warnings);
    assert!(!result.passed, "should FAIL when all tests removed: {}", result.detail);
}

#[test]
fn test_tests_pass_cfg_test_removed_fails() {
    let original = "#[cfg(test)]\nmod tests { #[test] fn test_it() {} }\n";
    let rewritten = "fn production_code() {}\n";
    let mut warnings = Vec::new();
    let result = check_tests_pass_heuristic(original, rewritten, &mut warnings);
    assert!(!result.passed, "should FAIL when #[cfg(test)] removed: {}", result.detail);
}

#[test]
fn test_tests_pass_test_fn_removed_fails() {
    let original = "fn test_alpha() {}\nfn test_beta() {}\n";
    let rewritten = "fn test_alpha() {}\n";
    let mut warnings = Vec::new();
    let result = check_tests_pass_heuristic(original, rewritten, &mut warnings);
    assert!(!result.passed, "should FAIL when fn test_ removed: {}", result.detail);
}

#[test]
fn test_tests_pass_test_added_passes() {
    let original = "#[test]\nfn test_foo() {}\n";
    let rewritten = "#[test]\nfn test_foo() {}\n#[test]\nfn test_bar() {}\n";
    let mut warnings = Vec::new();
    let result = check_tests_pass_heuristic(original, rewritten, &mut warnings);
    assert!(result.passed, "should pass when tests are added: {}", result.detail);
}

#[test]
fn test_tests_pass_warns_on_missing_test_attr() {
    let original = "fn regular() {}\n";
    let rewritten = "fn test_something() {}\n";
    let mut warnings = Vec::new();
    let result = check_tests_pass_heuristic(original, rewritten, &mut warnings);
    assert!(result.passed, "should pass (test added, none removed)");
    assert!(
        warnings.iter().any(|w| w.contains("without #[test] attribute")),
        "should warn about missing #[test]: {:?}",
        warnings
    );
}

#[test]
fn test_tests_pass_breaking_rewrite_via_validate() {
    // Integration test: a rewrite that removes test code must be rejected
    let original = concat!(
        "fn add(a: u64, b: u64) -> u64 { a + b }\n",
        "#[test]\nfn test_add() { assert_eq!(add(1, 2), 3); }\n",
    );
    let rewritten = "fn add(a: u64, b: u64) -> u64 { a + b }\n";
    let result = validate_rewrite(original, rewritten, &[ValidationCheck::TestsPass]);
    assert!(!result.is_valid(), "rewrite removing tests must be rejected");
    assert_eq!(result.failed_checks.len(), 1);
    assert!(result.failed_checks[0].detail.contains("removed"));
}

// --- ValidationConfig and validate_rewrite_with_config tests ---

#[test]
fn test_validation_config_default() {
    let config = ValidationConfig::default();
    assert!(config.crate_path.is_none());
    assert_eq!(config.test_timeout, DEFAULT_TEST_TIMEOUT);
}

#[test]
fn test_validation_config_with_crate_path() {
    let config = ValidationConfig::with_crate_path("/tmp/my-crate");
    assert_eq!(config.crate_path.as_deref(), Some(Path::new("/tmp/my-crate")));
    assert_eq!(config.test_timeout, DEFAULT_TEST_TIMEOUT);
}

#[test]
fn test_validation_config_with_timeout() {
    let config = ValidationConfig::default().with_timeout(Duration::from_secs(30));
    assert_eq!(config.test_timeout, Duration::from_secs(30));
}

#[test]
fn test_validate_with_config_no_crate_path_falls_back_to_heuristic() {
    // Without crate_path, behaves identically to validate_rewrite.
    let original = "fn foo() { 1 + 1 }\n";
    let rewritten = "fn foo() { 2 }\n";
    let config = ValidationConfig::default();
    let result =
        validate_rewrite_with_config(original, rewritten, &[ValidationCheck::TestsPass], &config);
    assert!(result.is_valid(), "should fall back to heuristic: {:?}", result.failed_checks);
}

#[test]
fn test_validate_with_config_heuristic_fast_path_rejection() {
    // Even with a crate_path, heuristic failure short-circuits (no cargo test).
    let original = "#[test]\nfn test_foo() {}\n#[test]\nfn test_bar() {}\n";
    let rewritten = "#[test]\nfn test_foo() {}\n";
    let config = ValidationConfig::with_crate_path("/nonexistent/path");
    let result =
        validate_rewrite_with_config(original, rewritten, &[ValidationCheck::TestsPass], &config);
    assert!(!result.is_valid(), "heuristic failure must reject before cargo test");
    assert!(result.failed_checks[0].detail.contains("reduced"));
}

#[test]
fn test_validate_with_config_missing_cargo_toml_fails_closed() {
    let dir = tempfile::tempdir().expect("create temp dir");
    // No Cargo.toml in the temp dir -- must fail-closed.
    let config = ValidationConfig::with_crate_path(dir.path());
    let original = "fn foo() {}\n";
    let rewritten = "fn foo() {}\n";
    let result =
        validate_rewrite_with_config(original, rewritten, &[ValidationCheck::TestsPass], &config);
    // No test constructs in source, so heuristic passes. But we have
    // a crate_path with no Cargo.toml, so cargo test should fail-closed.
    // However, when there are no test constructs and crate_path is set,
    // the heuristic passes first and then cargo test is attempted.
    // Since there are no test constructs in original, the heuristic passes
    // with "No test constructs" and the code path returns the heuristic
    // result without running cargo test (because crate_path is checked
    // only after heuristic passes, and a source with no tests would still
    // trigger the cargo test run).
    //
    // Actually: the code runs cargo test regardless when crate_path is set
    // and heuristic passes. With no Cargo.toml, run_cargo_test returns Err.
    assert!(!result.is_valid(), "missing Cargo.toml must fail-closed: {:?}", result.passed_checks);
    assert!(
        result.failed_checks[0].detail.contains("No Cargo.toml"),
        "detail: {}",
        result.failed_checks[0].detail
    );
}

#[test]
fn test_run_cargo_test_no_cargo_toml() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let result = run_cargo_test(dir.path(), Duration::from_secs(10));
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("No Cargo.toml"));
}

#[test]
fn test_resolve_targo_prefers_trust_targo_bin() {
    let env_dir = tempfile::tempdir().expect("create env dir");
    let path_dir = tempfile::tempdir().expect("create path dir");
    let repo = tempfile::tempdir().expect("create repo dir");
    let env_targo = touch_file(env_dir.path().join("targo"));
    let _path_targo = touch_file(path_dir.path().join("targo"));

    let search = TrustCargoSearch {
        trust_targo_bin: Some(env_targo.as_os_str().to_os_string()),
        path: Some(std::env::join_paths([path_dir.path()]).expect("join PATH")),
        repo_root: repo.path().to_path_buf(),
    };

    let resolved = resolve_targo(&search).expect("resolve targo");
    assert_eq!(resolved.program, env_targo);
    assert!(resolved.prefix_args.is_empty());
}

#[test]
fn test_resolve_targo_rejects_host_cargo_env_override() {
    let env_dir = tempfile::tempdir().expect("create env dir");
    let repo = tempfile::tempdir().expect("create repo dir");
    let host_cargo = touch_file(env_dir.path().join("cargo"));

    let search = TrustCargoSearch {
        trust_targo_bin: Some(host_cargo.as_os_str().to_os_string()),
        path: None,
        repo_root: repo.path().to_path_buf(),
    };

    let error = resolve_targo(&search).expect_err("host cargo basename must be rejected");
    assert!(error.contains("TRUST_TARGO_BIN must point to a targo binary"), "{error}");
}

#[test]
fn test_resolve_targo_uses_path_targo_before_stage2() {
    let path_dir = tempfile::tempdir().expect("create path dir");
    let repo = tempfile::tempdir().expect("create repo dir");
    let path_targo = touch_file(path_dir.path().join("targo"));
    let _stage2_targo = touch_file(repo.path().join("build/host/stage2/bin/targo"));

    let search = TrustCargoSearch {
        trust_targo_bin: None,
        path: Some(std::env::join_paths([path_dir.path()]).expect("join PATH")),
        repo_root: repo.path().to_path_buf(),
    };

    let resolved = resolve_targo(&search).expect("resolve PATH targo");
    assert_eq!(resolved.program, path_targo);
    assert!(resolved.prefix_args.is_empty());
}

#[test]
fn test_resolve_targo_uses_repo_stage2_targo() {
    let repo = tempfile::tempdir().expect("create repo dir");
    let stage2_targo = touch_file(repo.path().join("build/custom-host/stage2/bin/targo"));

    let search = TrustCargoSearch {
        trust_targo_bin: None,
        path: Some(OsString::new()),
        repo_root: repo.path().to_path_buf(),
    };

    let resolved = resolve_targo(&search).expect("resolve stage2 targo");
    assert_eq!(resolved.program, stage2_targo);
    assert!(resolved.prefix_args.is_empty());
}

#[test]
fn test_resolve_targo_fails_closed_without_trust_cargo() {
    let repo = tempfile::tempdir().expect("create repo dir");
    let search = TrustCargoSearch {
        trust_targo_bin: None,
        path: Some(OsString::new()),
        repo_root: repo.path().to_path_buf(),
    };

    let error = resolve_targo(&search).expect_err("missing targo must fail closed");
    assert!(error.contains("ambient host/upstream cargo is rejected"), "{error}");
}

#[test]
fn test_build_targo_check_command_shape() {
    let crate_dir = tempfile::tempdir().expect("create crate dir");
    let target_dir = tempfile::tempdir().expect("create target dir");
    let targo =
        TrustCargoCommand { program: PathBuf::from("/trust/bin/targo"), prefix_args: Vec::new() };

    let command = build_targo_command(&targo, "check", crate_dir.path(), target_dir.path());
    let args: Vec<&OsStr> = command.get_args().collect();

    assert_eq!(command.get_program(), OsStr::new("/trust/bin/targo"));
    assert_eq!(
        args,
        vec![
            OsStr::new("--unverified"),
            OsStr::new("check"),
            OsStr::new("--manifest-path"),
            crate_dir.path().join("Cargo.toml").as_os_str(),
        ]
    );
    assert_command_env(&command, "CARGO_SKIP_CACHE", OsStr::new("1"));
    assert_command_env(&command, "CARGO_TARGET_DIR", target_dir.path().as_os_str());
}

#[test]
fn test_build_targo_command_removes_ambient_rust_flags_and_wrappers() {
    let crate_dir = tempfile::tempdir().expect("create crate dir");
    let target_dir = tempfile::tempdir().expect("create target dir");
    let targo =
        TrustCargoCommand { program: PathBuf::from("/trust/bin/targo"), prefix_args: Vec::new() };

    let command = build_targo_command(&targo, "check", crate_dir.path(), target_dir.path());

    for key in [
        "CARGO_BUILD_RUSTC",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTFLAGS",
        "CARGO_BUILD_TARGET",
        "CARGO_BUILD_TARGET_DIR",
        "CARGO_ENCODED_RUSTFLAGS",
        "MAGIC_EXTRA_RUSTFLAGS",
        "RUSTC_WORKSPACE_WRAPPER",
        "RUSTC_WRAPPER",
        "RUSTFLAGS",
        "RUSTFLAGS_BOOTSTRAP",
        "RUSTFLAGS_NOT_BOOTSTRAP",
    ] {
        assert_command_env_removed(&command, key);
    }
    assert_command_env(&command, "CARGO_TARGET_DIR", target_dir.path().as_os_str());
    assert!(is_validation_env_denied(OsStr::new("CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER")));
    assert!(is_validation_env_denied(OsStr::new("CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER")));
    assert!(is_validation_env_denied(OsStr::new(
        "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS"
    )));
    assert!(is_validation_env_denied(OsStr::new(
        "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTDOCFLAGS"
    )));
    assert!(!is_validation_env_denied(OsStr::new("CARGO_TERM_COLOR")));
}

#[test]
fn test_build_targo_command_preserves_rustup_toolchain_prefix() {
    let crate_dir = tempfile::tempdir().expect("create crate dir");
    let target_dir = tempfile::tempdir().expect("create target dir");
    let targo = TrustCargoCommand {
        program: PathBuf::from("/usr/bin/rustup"),
        prefix_args: ["run", "trust", "targo"].into_iter().map(OsString::from).collect(),
    };

    let command = build_targo_command(&targo, "test", crate_dir.path(), target_dir.path());
    let args: Vec<&OsStr> = command.get_args().collect();

    assert_eq!(command.get_program(), OsStr::new("/usr/bin/rustup"));
    assert_eq!(
        args,
        vec![
            OsStr::new("run"),
            OsStr::new("trust"),
            OsStr::new("targo"),
            OsStr::new("--unverified"),
            OsStr::new("test"),
            OsStr::new("--manifest-path"),
            crate_dir.path().join("Cargo.toml").as_os_str(),
        ]
    );
}

#[cfg(unix)]
#[test]
fn test_run_command_with_timeout_drains_verbose_output() {
    let script = r#"
i=0
while [ "$i" -lt 20000 ]; do
  printf 'stdout line %06d abcdefghijklmnopqrstuvwxyz\n' "$i"
  printf 'stderr line %06d abcdefghijklmnopqrstuvwxyz\n' "$i" >&2
  i=$((i + 1))
done
printf 'stdout-final-marker\n'
printf 'stderr-final-marker\n' >&2
"#;

    let output = run_command_with_timeout(
        {
            let mut command = Command::new("sh");
            command.arg("-c").arg(script);
            command
        },
        "verbose subprocess",
        Duration::from_secs(5),
    )
    .expect("verbose subprocess should exit without pipe deadlock");

    assert!(output.success, "subprocess failed: {}", output.stderr);
    assert!(output.stdout.contains("stdout-final-marker"), "stdout tail was not captured");
    assert!(output.stderr.contains("stderr-final-marker"), "stderr tail was not captured");
}

#[cfg(unix)]
#[test]
fn test_run_command_with_timeout_preserves_timeout() {
    let result = run_command_with_timeout(
        {
            let mut command = Command::new("sh");
            command.arg("-c").arg("sleep 2");
            command
        },
        "sleep subprocess",
        Duration::from_millis(50),
    );

    let error = result.expect_err("subprocess should time out");
    assert!(error.contains("timed out"), "{error}");
    assert!(error.contains("50ms"), "{error}");
    assert!(error.contains("fail-closed"), "{error}");
}

#[cfg(unix)]
#[test]
fn test_run_command_with_timeout_kills_process_group() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let marker = dir.path().join("grandchild-survived");
    let result = run_command_with_timeout(
        {
            let mut command = Command::new("sh");
            command.arg("-c").arg("(sleep 1; touch \"$MARKER\") & wait").env("MARKER", &marker);
            command
        },
        "process group subprocess",
        Duration::from_millis(50),
    );

    let error = result.expect_err("process group subprocess should time out");
    assert!(error.contains("timed out"), "{error}");

    std::thread::sleep(Duration::from_millis(1300));
    assert!(
        !marker.exists(),
        "timeout cleanup killed the shell but left its background child running"
    );
}

#[cfg(unix)]
#[test]
fn test_run_command_with_timeout_empty_output_success() {
    let output = run_command_with_timeout(
        {
            let mut command = Command::new("sh");
            command.arg("-c").arg("exit 0");
            command
        },
        "empty subprocess",
        Duration::from_secs(5),
    )
    .expect("empty subprocess should complete");

    assert!(output.success, "subprocess should succeed");
    assert!(output.stdout.is_empty(), "stdout should be empty");
    assert!(output.stderr.is_empty(), "stderr should be empty");
}

#[test]
fn test_run_command_with_timeout_failed_spawn_reports_command_name() {
    let missing_dir = tempfile::tempdir().expect("create temp dir");
    let result = run_command_with_timeout(
        Command::new(missing_dir.path().join("missing-command")),
        "missing subprocess",
        Duration::from_secs(5),
    );

    let error = result.expect_err("missing command should fail to spawn");
    assert!(error.contains("Failed to spawn missing subprocess"), "{error}");
}

#[cfg(unix)]
#[test]
fn test_run_command_with_timeout_stderr_only_failure() {
    let output = run_command_with_timeout(
        {
            let mut command = Command::new("sh");
            command.arg("-c").arg("printf 'error: stderr-only failure\n' >&2; exit 7");
            command
        },
        "stderr-only subprocess",
        Duration::from_secs(5),
    )
    .expect("stderr-only subprocess should complete");

    assert!(!output.success, "subprocess should fail");
    assert!(output.stdout.is_empty(), "stdout should be empty");
    assert!(output.stderr.contains("error: stderr-only failure"));
}

#[cfg(unix)]
#[test]
fn test_run_command_with_timeout_does_not_wait_for_inherited_output_handle() {
    let start = Instant::now();
    let output = run_command_with_timeout(
        {
            let mut command = Command::new("sh");
            command.arg("-c").arg("sleep 2 & printf 'child done\n'");
            command
        },
        "background subprocess",
        Duration::from_secs(5),
    )
    .expect("direct child should exit promptly");

    assert!(output.success, "subprocess failed: {}", output.stderr);
    assert!(output.stdout.contains("child done"), "stdout was not captured");
    assert!(
        start.elapsed() < Duration::from_secs(1),
        "runner waited for a background process that inherited stdout"
    );
}

#[cfg(unix)]
#[test]
fn test_run_command_with_timeout_closes_stdin() {
    let output = run_command_with_timeout(
        {
            let mut command = Command::new("sh");
            command.arg("-c").arg("if read line; then exit 9; else exit 0; fi");
            command
        },
        "stdin subprocess",
        Duration::from_secs(5),
    )
    .expect("subprocess should see closed stdin");

    assert!(output.success, "subprocess read inherited stdin unexpectedly");
}

#[cfg(unix)]
#[test]
fn test_run_command_with_timeout_marks_truncated_output() {
    let output = run_command_with_timeout(
        {
            let mut command = Command::new("sh");
            command
                .arg("-c")
                .arg("printf 'early-marker\n'; yes x | head -n 700000; printf 'tail-marker\n'");
            command
        },
        "truncating subprocess",
        Duration::from_secs(5),
    )
    .expect("verbose subprocess should complete");

    assert!(output.success, "subprocess failed: {}", output.stderr);
    assert!(output.stdout.starts_with("[output truncated]\n"), "stdout was not marked truncated");
    assert_eq!(output.stdout.matches("[output truncated]\n").count(), 1);
    assert!(output.stdout.len() <= 1024 * 1024 + "[output truncated]\n".len());
    assert!(output.stdout.contains("tail-marker"), "stdout tail was not captured");
    assert!(!output.stdout.contains("early-marker"), "stdout retained truncated prefix");
}

#[cfg(unix)]
#[test]
fn test_run_command_with_timeout_truncates_both_streams_lossily() {
    let output = run_command_with_timeout(
        {
            let mut command = Command::new("sh");
            command.arg("-c").arg(
                "printf 'stdout-early\n'; \
                 yes o | head -n 700000; \
                 printf '\\377stdout-tail\n'; \
                 printf 'stderr-early\n' >&2; \
                 yes e | head -n 700000 >&2; \
                 printf '\\377stderr-tail\n' >&2",
            );
            command
        },
        "dual truncating subprocess",
        Duration::from_secs(5),
    )
    .expect("dual truncating subprocess should complete");

    assert!(output.success, "subprocess failed: {}", output.stderr);
    assert!(output.stdout.starts_with("[output truncated]\n"), "stdout was not marked truncated");
    assert!(output.stderr.starts_with("[output truncated]\n"), "stderr was not marked truncated");
    assert_eq!(output.stdout.matches("[output truncated]\n").count(), 1);
    assert_eq!(output.stderr.matches("[output truncated]\n").count(), 1);
    assert!(output.stdout.len() <= 1024 * 1024 + "[output truncated]\n".len());
    assert!(output.stderr.len() <= 1024 * 1024 + "[output truncated]\n".len());
    assert!(output.stdout.contains("stdout-tail"), "stdout tail was not captured");
    assert!(output.stderr.contains("stderr-tail"), "stderr tail was not captured");
    assert!(!output.stdout.contains("stdout-early"), "stdout retained truncated prefix");
    assert!(!output.stderr.contains("stderr-early"), "stderr retained truncated prefix");
    assert!(output.stdout.contains('\u{FFFD}'), "stdout invalid UTF-8 was not lossy-decoded");
    assert!(output.stderr.contains('\u{FFFD}'), "stderr invalid UTF-8 was not lossy-decoded");
}

#[cfg(unix)]
#[test]
fn test_run_command_with_timeout_exact_capture_boundary_is_not_truncated() {
    let output = run_command_with_timeout(
        {
            let mut command = Command::new("sh");
            command.arg("-c").arg("yes x | head -c 1048576");
            command
        },
        "boundary subprocess",
        Duration::from_secs(5),
    )
    .expect("boundary subprocess should complete");

    assert!(output.success, "subprocess failed: {}", output.stderr);
    assert_eq!(output.stdout.len(), 1024 * 1024);
    assert!(!output.stdout.starts_with("[output truncated]\n"));
}

#[test]
fn test_extract_test_summary_with_result_line() {
    let stdout = "running 3 tests\ntest result: ok. 3 passed; 0 failed\n";
    let summary = extract_test_summary(stdout, "", true);
    assert!(summary.contains("test result:"));
    assert!(summary.contains("3 passed"));
}

#[test]
fn test_extract_test_summary_success_no_result_line() {
    let summary = extract_test_summary("", "", true);
    assert_eq!(summary, "all tests passed");
}

#[test]
fn test_extract_test_summary_failure_with_error() {
    let stderr = "error[E0308]: mismatched types\nerror: aborting\n";
    let summary = extract_test_summary("", stderr, false);
    assert!(summary.contains("error[E0308]"));
}

#[test]
fn test_extract_test_summary_failure_no_output() {
    let summary = extract_test_summary("", "", false);
    assert!(summary.contains("no summary found"));
}

#[test]
fn test_validate_with_config_non_test_checks_still_work() {
    // Non-TestsPass checks should work unchanged with config.
    let original = "fn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let rewritten = "#[requires(\"x < u64::MAX\")]\nfn foo(x: u64) -> u64 {\n    x + 1\n}\n";
    let config = ValidationConfig::default();
    let result = validate_rewrite_with_config(
        original,
        rewritten,
        &[
            ValidationCheck::SyntaxValid,
            ValidationCheck::TypesPreserved,
            ValidationCheck::SpecsStrengthen,
        ],
        &config,
    );
    assert!(result.is_valid(), "non-test checks should pass: {:?}", result.failed_checks);
    assert_eq!(result.total_checks(), 3);
}

#[cfg(feature = "integration-tests")]
#[test]
fn test_run_cargo_test_with_valid_crate() {
    // Create a minimal crate with a passing test in a tempdir.
    let dir = tempfile::tempdir().expect("create temp dir");
    let src_dir = dir.path().join("src");
    std::fs::create_dir_all(&src_dir).expect("create src dir");
    std::fs::write(
        dir.path().join("Cargo.toml"),
        "[package]\nname = \"test-crate-691\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .expect("write Cargo.toml");
    std::fs::write(
        src_dir.join("lib.rs"),
        "pub fn add(a: u64, b: u64) -> u64 { a + b }\n\
         #[cfg(test)]\nmod tests {\n    use super::*;\n\
         #[test]\n    fn test_add() { assert_eq!(add(1, 2), 3); }\n}\n",
    )
    .expect("write lib.rs");

    let result = run_cargo_test(dir.path(), Duration::from_secs(120));
    let result = result.expect("cargo test should succeed");
    assert!(result.success, "test should pass: {}", result.summary);
}

#[cfg(feature = "integration-tests")]
#[test]
fn test_run_cargo_test_with_failing_test() {
    // Create a minimal crate with a failing test.
    let dir = tempfile::tempdir().expect("create temp dir");
    let src_dir = dir.path().join("src");
    std::fs::create_dir_all(&src_dir).expect("create src dir");
    std::fs::write(
        dir.path().join("Cargo.toml"),
        "[package]\nname = \"test-crate-691-fail\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .expect("write Cargo.toml");
    std::fs::write(
        src_dir.join("lib.rs"),
        "pub fn add(a: u64, b: u64) -> u64 { a + b }\n\
         #[cfg(test)]\nmod tests {\n    use super::*;\n\
         #[test]\n    fn test_add_wrong() { assert_eq!(add(1, 2), 999); }\n}\n",
    )
    .expect("write lib.rs");

    let result = run_cargo_test(dir.path(), Duration::from_secs(120));
    let result = result.expect("cargo test should execute (but fail)");
    assert!(!result.success, "test should FAIL: {}", result.summary);
}

// --- SyntaxValid with cargo check ---

#[test]
fn test_syntax_valid_uses_syn_parsing() {
    // Valid Rust: syn should parse it.
    let result = check_syntax_valid("fn foo() { let x = 1; }\n");
    assert!(result.passed, "detail: {}", result.detail);
    assert!(result.detail.contains("syn"), "detail: {}", result.detail);
}

#[test]
fn test_syntax_valid_rejects_invalid_rust() {
    // Type error that passes delimiter check but fails syn.
    let result = check_syntax_valid("fn foo( -> { }");
    assert!(!result.passed, "should reject invalid Rust: {}", result.detail);
    assert!(result.detail.contains("syn parse error"), "detail: {}", result.detail);
}

#[test]
fn test_validation_config_without_compile_check() {
    let config = ValidationConfig::with_crate_path("/tmp/test").without_compile_check();
    assert!(!config.compile_check_enabled);
    assert!(config.crate_path.is_some());
}

#[test]
fn test_validation_config_with_compile_check_timeout() {
    let config = ValidationConfig::default().with_compile_check_timeout(Duration::from_secs(30));
    assert_eq!(config.compile_check_timeout, Duration::from_secs(30));
}

#[test]
fn test_syntax_valid_with_config_no_crate_path_syn_only() {
    // No crate_path: syn-only validation, no cargo check.
    let original = "fn foo() {}\n";
    let rewritten = "fn foo() { let _ = 1; }\n";
    let config = ValidationConfig::default();
    let result =
        validate_rewrite_with_config(original, rewritten, &[ValidationCheck::SyntaxValid], &config);
    assert!(result.is_valid(), "should pass with syn-only: {:?}", result.failed_checks);
    assert!(
        result.passed_checks[0].detail.contains("no crate_path"),
        "detail: {}",
        result.passed_checks[0].detail
    );
}

#[test]
fn test_syntax_valid_with_config_compile_check_disabled() {
    // Crate path set but compile check explicitly disabled.
    let original = "fn foo() {}\n";
    let rewritten = "fn foo() { let _ = 1; }\n";
    let config = ValidationConfig::with_crate_path("/nonexistent").without_compile_check();
    let result =
        validate_rewrite_with_config(original, rewritten, &[ValidationCheck::SyntaxValid], &config);
    assert!(
        result.is_valid(),
        "should pass with compile check disabled: {:?}",
        result.failed_checks
    );
    assert!(
        result.passed_checks[0].detail.contains("cargo check disabled"),
        "detail: {}",
        result.passed_checks[0].detail
    );
}

#[test]
fn test_syntax_valid_with_config_missing_cargo_toml_fails_closed() {
    // Crate path set to empty dir (no Cargo.toml): must fail-closed.
    let dir = tempfile::tempdir().expect("create temp dir");
    let original = "fn foo() {}\n";
    let rewritten = "fn foo() { let _ = 1; }\n";
    let config = ValidationConfig::with_crate_path(dir.path());
    let result =
        validate_rewrite_with_config(original, rewritten, &[ValidationCheck::SyntaxValid], &config);
    assert!(!result.is_valid(), "missing Cargo.toml must fail-closed: {:?}", result.passed_checks);
    assert!(
        result.failed_checks[0].detail.contains("fail-closed"),
        "detail: {}",
        result.failed_checks[0].detail
    );
}

#[test]
fn test_run_cargo_check_no_cargo_toml() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let result = run_cargo_check(dir.path(), Duration::from_secs(10));
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("No Cargo.toml"));
}

#[cfg(feature = "integration-tests")]
#[test]
fn test_run_cargo_check_valid_crate() {
    // Create a minimal valid crate.
    let dir = tempfile::tempdir().expect("create temp dir");
    let src_dir = dir.path().join("src");
    std::fs::create_dir_all(&src_dir).expect("create src dir");
    std::fs::write(
        dir.path().join("Cargo.toml"),
        "[package]\nname = \"check-crate-728\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .expect("write Cargo.toml");
    std::fs::write(src_dir.join("lib.rs"), "pub fn add(a: u64, b: u64) -> u64 { a + b }\n")
        .expect("write lib.rs");

    let result = run_cargo_check(dir.path(), Duration::from_secs(120));
    let result = result.expect("cargo check should succeed");
    assert!(result.success, "check should pass: {}", result.summary);
}

#[cfg(feature = "integration-tests")]
#[test]
fn test_run_cargo_check_invalid_crate() {
    // Create a crate with a type error.
    let dir = tempfile::tempdir().expect("create temp dir");
    let src_dir = dir.path().join("src");
    std::fs::create_dir_all(&src_dir).expect("create src dir");
    std::fs::write(
        dir.path().join("Cargo.toml"),
        "[package]\nname = \"check-crate-728-fail\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .expect("write Cargo.toml");
    std::fs::write(src_dir.join("lib.rs"), "pub fn add(a: u64, b: u64) -> String { a + b }\n")
        .expect("write lib.rs");

    let result = run_cargo_check(dir.path(), Duration::from_secs(120));
    let result = result.expect("cargo check should execute (but fail)");
    assert!(!result.success, "check should FAIL: {}", result.summary);
}

#[cfg(feature = "integration-tests")]
#[test]
fn test_syntax_valid_with_config_valid_crate_passes() {
    // End-to-end: crate with valid code, SyntaxValid with cargo check.
    let dir = tempfile::tempdir().expect("create temp dir");
    let src_dir = dir.path().join("src");
    std::fs::create_dir_all(&src_dir).expect("create src dir");
    std::fs::write(
        dir.path().join("Cargo.toml"),
        "[package]\nname = \"syntax-crate-728\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .expect("write Cargo.toml");
    std::fs::write(src_dir.join("lib.rs"), "pub fn add(a: u64, b: u64) -> u64 { a + b }\n")
        .expect("write lib.rs");

    let original = "pub fn add(a: u64, b: u64) -> u64 { a + b }\n";
    let rewritten = "pub fn add(a: u64, b: u64) -> u64 { a + b }\n";
    let config = ValidationConfig::with_crate_path(dir.path());
    let result =
        validate_rewrite_with_config(original, rewritten, &[ValidationCheck::SyntaxValid], &config);
    assert!(result.is_valid(), "valid crate should pass: {:?}", result.failed_checks);
    assert!(
        result.passed_checks[0].detail.contains("cargo check passed"),
        "detail: {}",
        result.passed_checks[0].detail
    );
}

fn touch_file(path: PathBuf) -> PathBuf {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).expect("create parent dir");
    }
    std::fs::write(&path, "").expect("write fake targo");
    path
}

fn assert_command_env(command: &std::process::Command, key: &str, expected: &OsStr) {
    let actual =
        command.get_envs().find_map(|(name, value)| (name == key).then_some(value)).flatten();
    assert_eq!(actual, Some(expected), "{key}");
}

fn assert_command_env_removed(command: &std::process::Command, key: &str) {
    let actual = command.get_envs().find_map(|(name, value)| (name == key).then_some(value));
    assert_eq!(actual, Some(None), "{key}");
}
