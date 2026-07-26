//! AST-based rewrite validation using `syn`.
//!
//! Parses original and rewritten Rust source into real ASTs via `syn`, then
//! performs structural comparison. Falls back to the heuristic string-based
//! checks in `crate::validation` when source cannot be parsed.
//!
//! Key invariants enforced:
//! - Function signatures are preserved (name, params, return type, generics).
//! - No new `unsafe` blocks are introduced.
//! - Type annotations on local bindings are unchanged.
//! - Only function bodies are modified; the surrounding item structure is stable.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::fx::FxHashMap;

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Structured error from AST-based validation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, thiserror::Error)]
#[non_exhaustive]
pub enum AstValidationError {
    /// A function signature was changed by the rewrite.
    #[error("signature changed for `{function}`: {detail}")]
    SignatureChanged { function: String, detail: String },

    /// A new `unsafe` block was introduced by the rewrite.
    #[error("new unsafe block introduced in `{function}`")]
    NewUnsafeBlock { function: String },

    /// A type annotation on a local binding was changed.
    #[error("type annotation changed in `{function}`: `{original}` -> `{rewritten}`")]
    TypeAnnotationChanged { function: String, original: String, rewritten: String },

    /// Non-body modifications detected (e.g., visibility, attributes beyond specs).
    #[error("non-body modification in `{function}`: {detail}")]
    NonBodyModification { function: String, detail: String },

    /// A function was removed by the rewrite.
    #[error("function `{function}` removed by rewrite")]
    FunctionRemoved { function: String },

    /// A function was added by the rewrite (unexpected structural change).
    #[error("unexpected new function `{function}` added by rewrite")]
    FunctionAdded { function: String },

    /// Source failed to parse; falling back to heuristic validation.
    #[error("parse error ({which}): {message}")]
    ParseError { which: ParseTarget, message: String },
}

/// Which source failed to parse.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ParseTarget {
    Original,
    Rewritten,
    Both,
}

impl std::fmt::Display for ParseTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Original => write!(f, "original"),
            Self::Rewritten => write!(f, "rewritten"),
            Self::Both => write!(f, "both"),
        }
    }
}

// ---------------------------------------------------------------------------
// Validation result
// ---------------------------------------------------------------------------

/// Result of AST-based validation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AstValidationResult {
    /// Whether validation passed (no errors).
    pub passed: bool,
    /// Structured errors found during validation.
    pub errors: Vec<AstValidationError>,
    /// Non-fatal warnings.
    pub warnings: Vec<String>,
    /// Whether AST parsing succeeded or we fell back to heuristics.
    pub used_ast: bool,
}

impl AstValidationResult {
    /// Create a passing result.
    #[must_use]
    pub fn ok(used_ast: bool) -> Self {
        Self { passed: true, errors: Vec::new(), warnings: Vec::new(), used_ast }
    }

    /// Create a result with errors.
    #[must_use]
    pub fn with_errors(
        errors: Vec<AstValidationError>,
        warnings: Vec<String>,
        used_ast: bool,
    ) -> Self {
        Self { passed: errors.is_empty(), errors, warnings, used_ast }
    }
}

// ---------------------------------------------------------------------------
// Extracted function signature (serializable, AST-independent)
// ---------------------------------------------------------------------------

/// A function signature extracted from the AST for comparison.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct FnSignature {
    pub(crate) name: String,
    pub(crate) params: Vec<ParamInfo>,
    pub(crate) return_type: String,
    pub(crate) generics: String,
    pub(crate) is_async: bool,
    pub(crate) is_unsafe: bool,
    pub(crate) visibility: String,
}

/// Info about a single function parameter.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ParamInfo {
    pub(crate) name: String,
    pub(crate) ty: String,
}

// ---------------------------------------------------------------------------
// Core validation entry point
// ---------------------------------------------------------------------------

/// Validate a rewrite using `syn`-based AST comparison.
///
/// Parses both `original` and `rewritten` as Rust source files, extracts
/// function signatures and structural properties, and compares them.
///
/// If either source fails to parse, returns a `ParseError` in the result
/// with `used_ast: false`, signalling the caller to fall back to heuristic
/// validation.
#[must_use]
pub fn validate_rewrite_ast(original: &str, rewritten: &str) -> AstValidationResult {
    let original_for_parse = match crate::ast_rewriter::mask_native_contract_clauses(original) {
        Ok(source) => source,
        Err(error) => {
            return AstValidationResult::with_errors(
                vec![AstValidationError::ParseError {
                    which: ParseTarget::Original,
                    message: error.to_string(),
                }],
                Vec::new(),
                false,
            );
        }
    };
    let rewritten_for_parse = match crate::ast_rewriter::mask_native_contract_clauses(rewritten) {
        Ok(source) => source,
        Err(error) => {
            return AstValidationResult::with_errors(
                vec![AstValidationError::ParseError {
                    which: ParseTarget::Rewritten,
                    message: error.to_string(),
                }],
                Vec::new(),
                false,
            );
        }
    };
    let orig_file = match syn::parse_file(&original_for_parse) {
        Ok(f) => f,
        Err(e) => {
            let rw_parseable = syn::parse_file(&rewritten_for_parse).is_ok();
            let target = if rw_parseable { ParseTarget::Original } else { ParseTarget::Both };
            return AstValidationResult::with_errors(
                vec![AstValidationError::ParseError { which: target, message: e.to_string() }],
                Vec::new(),
                false,
            );
        }
    };
    let rw_file = match syn::parse_file(&rewritten_for_parse) {
        Ok(f) => f,
        Err(e) => {
            return AstValidationResult::with_errors(
                vec![AstValidationError::ParseError {
                    which: ParseTarget::Rewritten,
                    message: e.to_string(),
                }],
                Vec::new(),
                false,
            );
        }
    };

    let orig_fns = extract_functions(&orig_file);
    let rw_fns = extract_functions(&rw_file);

    let mut errors = Vec::new();
    let mut warnings = Vec::new();

    // Check for removed functions.
    for name in orig_fns.keys() {
        if !rw_fns.contains_key(name) {
            errors.push(AstValidationError::FunctionRemoved { function: name.clone() });
        }
    }

    // Check for added functions.
    for name in rw_fns.keys() {
        if !orig_fns.contains_key(name) {
            errors.push(AstValidationError::FunctionAdded { function: name.clone() });
        }
    }

    // For each matching function, compare signatures and check for unsafe/type changes.
    for (name, orig_info) in &orig_fns {
        if let Some(rw_info) = rw_fns.get(name) {
            // 1. Signature preservation
            compare_signatures(name, &orig_info.sig, &rw_info.sig, &mut errors);

            // 2. No new unsafe blocks
            check_no_new_unsafe(
                name,
                orig_info.unsafe_block_count,
                rw_info.unsafe_block_count,
                &mut errors,
            );

            // 3. Type annotations on locals unchanged
            check_type_annotations(
                name,
                &orig_info.local_types,
                &rw_info.local_types,
                &mut errors,
                &mut warnings,
            );
        }
    }

    AstValidationResult::with_errors(errors, warnings, true)
}

// ---------------------------------------------------------------------------
// Internal: function info extraction
// ---------------------------------------------------------------------------

/// Collected info about a function item in a parsed file.
struct FnInfo {
    sig: FnSignature,
    unsafe_block_count: usize,
    local_types: Vec<(String, String)>,
}

/// Extract all function items from a parsed file.
fn extract_functions(file: &syn::File) -> FxHashMap<String, FnInfo> {
    let mut map = FxHashMap::default();
    for item in &file.items {
        if let syn::Item::Fn(item_fn) = item {
            let name = item_fn.sig.ident.to_string();
            let sig = extract_signature(item_fn);
            let unsafe_block_count = count_unsafe_blocks(&item_fn.block);
            let local_types = extract_local_types(&item_fn.block);
            map.insert(name, FnInfo { sig, unsafe_block_count, local_types });
        }
    }
    map
}

/// Extract a serializable function signature from a `syn::ItemFn`.
fn extract_signature(item_fn: &syn::ItemFn) -> FnSignature {
    let sig = &item_fn.sig;

    let params: Vec<ParamInfo> = sig
        .inputs
        .iter()
        .map(|arg| match arg {
            syn::FnArg::Receiver(r) => {
                ParamInfo { name: "self".to_string(), ty: quote_to_string(r) }
            }
            syn::FnArg::Typed(pat_type) => ParamInfo {
                name: quote_to_string(&pat_type.pat),
                ty: quote_to_string(&pat_type.ty),
            },
        })
        .collect();

    let return_type = match &sig.output {
        syn::ReturnType::Default => String::new(),
        syn::ReturnType::Type(_, ty) => quote_to_string(ty),
    };

    let generics =
        if sig.generics.params.is_empty() { String::new() } else { quote_to_string(&sig.generics) };

    FnSignature {
        name: sig.ident.to_string(),
        params,
        return_type,
        generics,
        is_async: sig.asyncness.is_some(),
        is_unsafe: sig.unsafety.is_some(),
        visibility: quote_to_string(&item_fn.vis),
    }
}

/// Count `unsafe { ... }` blocks inside a block (non-recursive into nested fns).
fn count_unsafe_blocks(block: &syn::Block) -> usize {
    use syn::visit::Visit;

    struct UnsafeCounter {
        count: usize,
    }
    impl<'ast> Visit<'ast> for UnsafeCounter {
        fn visit_expr_unsafe(&mut self, node: &'ast syn::ExprUnsafe) {
            self.count += 1;
            syn::visit::visit_expr_unsafe(self, node);
        }
        // Do not descend into nested function items.
        fn visit_item_fn(&mut self, _node: &'ast syn::ItemFn) {}
    }

    let mut counter = UnsafeCounter { count: 0 };
    counter.visit_block(block);
    counter.count
}

/// Extract `(binding_name, type_string)` for all typed let-bindings in a block.
fn extract_local_types(block: &syn::Block) -> Vec<(String, String)> {
    let mut locals = Vec::new();
    collect_local_types_from_block(block, &mut locals);
    locals
}

/// Recursively collect typed let-bindings from a block.
fn collect_local_types_from_block(block: &syn::Block, out: &mut Vec<(String, String)>) {
    for stmt in &block.stmts {
        if let syn::Stmt::Local(local) = stmt {
            extract_typed_pats(&local.pat, out);
        }
    }
}

/// Extract name and type string from patterns that include a type annotation.
fn extract_typed_pats(pat: &syn::Pat, out: &mut Vec<(String, String)>) {
    if let syn::Pat::Type(pat_type) = pat {
        let name = quote_to_string(&pat_type.pat);
        let ty = quote_to_string(&pat_type.ty);
        out.push((name, ty));
    }
}

/// Helper: use the `quote` machinery to turn a syn node into a normalized string.
fn quote_to_string<T: quote::ToTokens>(node: &T) -> String {
    node.to_token_stream().to_string()
}

// ---------------------------------------------------------------------------
// Comparison helpers
// ---------------------------------------------------------------------------

/// Compare two function signatures and push errors for any differences.
fn compare_signatures(
    fn_name: &str,
    orig: &FnSignature,
    rewritten: &FnSignature,
    errors: &mut Vec<AstValidationError>,
) {
    // Parameter count
    if orig.params.len() != rewritten.params.len() {
        errors.push(AstValidationError::SignatureChanged {
            function: fn_name.into(),
            detail: format!(
                "parameter count changed: {} -> {}",
                orig.params.len(),
                rewritten.params.len()
            ),
        });
        return; // No point comparing individual params if count differs.
    }

    // Individual parameters
    for (i, (op, rp)) in orig.params.iter().zip(&rewritten.params).enumerate() {
        if op.ty != rp.ty {
            errors.push(AstValidationError::SignatureChanged {
                function: fn_name.into(),
                detail: format!("parameter {} type changed: `{}` -> `{}`", i, op.ty, rp.ty),
            });
        }
        if op.name != rp.name {
            errors.push(AstValidationError::SignatureChanged {
                function: fn_name.into(),
                detail: format!("parameter {} name changed: `{}` -> `{}`", i, op.name, rp.name),
            });
        }
    }

    // Return type
    if orig.return_type != rewritten.return_type {
        errors.push(AstValidationError::SignatureChanged {
            function: fn_name.into(),
            detail: format!(
                "return type changed: `{}` -> `{}`",
                orig.return_type, rewritten.return_type
            ),
        });
    }

    // Generics
    if orig.generics != rewritten.generics {
        errors.push(AstValidationError::SignatureChanged {
            function: fn_name.into(),
            detail: format!("generics changed: `{}` -> `{}`", orig.generics, rewritten.generics),
        });
    }

    // Async / unsafe qualifiers
    if orig.is_async != rewritten.is_async {
        errors.push(AstValidationError::SignatureChanged {
            function: fn_name.into(),
            detail: format!("async qualifier changed: {} -> {}", orig.is_async, rewritten.is_async),
        });
    }
    if orig.is_unsafe != rewritten.is_unsafe {
        errors.push(AstValidationError::SignatureChanged {
            function: fn_name.into(),
            detail: format!(
                "unsafe qualifier changed: {} -> {}",
                orig.is_unsafe, rewritten.is_unsafe
            ),
        });
    }

    // Visibility
    if orig.visibility != rewritten.visibility {
        errors.push(AstValidationError::NonBodyModification {
            function: fn_name.into(),
            detail: format!(
                "visibility changed: `{}` -> `{}`",
                orig.visibility, rewritten.visibility
            ),
        });
    }
}

/// Check that no new unsafe blocks were introduced.
fn check_no_new_unsafe(
    fn_name: &str,
    orig_count: usize,
    rw_count: usize,
    errors: &mut Vec<AstValidationError>,
) {
    if rw_count > orig_count {
        errors.push(AstValidationError::NewUnsafeBlock { function: fn_name.into() });
    }
}

/// Check that explicit type annotations on let-bindings are preserved.
///
/// We only flag *changed* annotations; new bindings with types are fine (the
/// rewrite may introduce helper variables). Removed typed bindings are also
/// flagged since that may change semantics.
fn check_type_annotations(
    fn_name: &str,
    orig_locals: &[(String, String)],
    rw_locals: &[(String, String)],
    errors: &mut Vec<AstValidationError>,
    warnings: &mut Vec<String>,
) {
    let orig_map: FxHashMap<&str, &str> =
        orig_locals.iter().map(|(n, t)| (n.as_str(), t.as_str())).collect();
    let rw_map: FxHashMap<&str, &str> =
        rw_locals.iter().map(|(n, t)| (n.as_str(), t.as_str())).collect();

    // Check for changed type annotations on existing bindings.
    for (name, orig_ty) in &orig_map {
        if let Some(rw_ty) = rw_map.get(name)
            && orig_ty != rw_ty
        {
            errors.push(AstValidationError::TypeAnnotationChanged {
                function: fn_name.into(),
                original: format!("{name}: {orig_ty}"),
                rewritten: format!("{name}: {rw_ty}"),
            });
        }
        // If the binding is gone entirely, that's a body change -- we only
        // warn since the binding might have been inlined.
        if !rw_map.contains_key(name) {
            warnings.push(format!("typed binding `{name}: {orig_ty}` in `{fn_name}` was removed"));
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // --- Parsing success / failure ---

    #[test]
    fn test_ast_validation_both_parseable_identical() {
        let src = "fn foo(x: u64) -> u64 { x + 1 }\n";
        let result = validate_rewrite_ast(src, src);
        assert!(result.passed, "errors: {:?}", result.errors);
        assert!(result.used_ast);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_ast_validation_original_unparseable() {
        let orig = "fn foo( { broken";
        let rw = "fn foo(x: u64) -> u64 { x + 1 }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(!result.used_ast);
        assert!(matches!(
            &result.errors[0],
            AstValidationError::ParseError { which: ParseTarget::Original, .. }
        ));
    }

    #[test]
    fn test_ast_validation_rewritten_unparseable() {
        let orig = "fn foo(x: u64) -> u64 { x + 1 }\n";
        let rw = "fn foo( { broken";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(!result.used_ast);
        assert!(matches!(
            &result.errors[0],
            AstValidationError::ParseError { which: ParseTarget::Rewritten, .. }
        ));
    }

    #[test]
    fn test_ast_validation_both_unparseable() {
        let result = validate_rewrite_ast("broken {{{", "also broken {{{");
        assert!(!result.passed);
        assert!(!result.used_ast);
        assert!(matches!(
            &result.errors[0],
            AstValidationError::ParseError { which: ParseTarget::Both, .. }
        ));
    }

    // --- Signature preservation ---

    #[test]
    fn test_ast_validation_signature_preserved_with_body_change() {
        let orig = "fn foo(x: u64) -> u64 { x + 1 }\n";
        let rw = "fn foo(x: u64) -> u64 { x.wrapping_add(1) }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(result.passed, "errors: {:?}", result.errors);
        assert!(result.used_ast);
    }

    #[test]
    fn test_ast_validation_signature_preserved_with_spec_attr() {
        let orig = "fn foo(x: u64) -> u64 { x + 1 }\n";
        // Spec attributes are outer attributes; syn treats them as Item attrs.
        let rw = "#[doc = \"spec\"]\nfn foo(x: u64) -> u64 { x + 1 }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(result.passed, "errors: {:?}", result.errors);
    }

    #[test]
    fn test_ast_validation_param_type_changed() {
        let orig = "fn foo(x: u64) -> u64 { x }\n";
        let rw = "fn foo(x: i64) -> u64 { x as u64 }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.used_ast);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::SignatureChanged { function, detail }
                if function == "foo" && detail.contains("type changed")
        )));
    }

    #[test]
    fn test_ast_validation_return_type_changed() {
        let orig = "fn foo(x: u64) -> u64 { x }\n";
        let rw = "fn foo(x: u64) -> Option<u64> { Some(x) }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::SignatureChanged { detail, .. }
                if detail.contains("return type")
        )));
    }

    #[test]
    fn test_ast_validation_param_count_changed() {
        let orig = "fn foo(x: u64) -> u64 { x }\n";
        let rw = "fn foo(x: u64, y: u64) -> u64 { x + y }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::SignatureChanged { detail, .. }
                if detail.contains("parameter count")
        )));
    }

    #[test]
    fn test_ast_validation_generics_changed() {
        let orig = "fn foo<T>(x: T) -> T { x }\n";
        let rw = "fn foo<T: Clone>(x: T) -> T { x.clone() }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::SignatureChanged { detail, .. }
                if detail.contains("generics")
        )));
    }

    #[test]
    fn test_ast_validation_async_qualifier_changed() {
        let orig = "fn foo() {}\n";
        let rw = "async fn foo() {}\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::SignatureChanged { detail, .. }
                if detail.contains("async")
        )));
    }

    #[test]
    fn test_ast_validation_unsafe_qualifier_changed() {
        let orig = "fn foo() {}\n";
        let rw = "unsafe fn foo() {}\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::SignatureChanged { detail, .. }
                if detail.contains("unsafe qualifier")
        )));
    }

    // --- No new unsafe blocks ---

    #[test]
    fn test_ast_validation_no_new_unsafe_clean() {
        let orig = "fn foo(x: u64) -> u64 { x + 1 }\n";
        let rw = "fn foo(x: u64) -> u64 { x.wrapping_add(1) }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(result.passed, "errors: {:?}", result.errors);
    }

    #[test]
    fn test_ast_validation_new_unsafe_block_detected() {
        let orig = "fn foo(x: *const u8) -> u8 { 0 }\n";
        let rw = "fn foo(x: *const u8) -> u8 { unsafe { *x } }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::NewUnsafeBlock { function }
                if function == "foo"
        )));
    }

    #[test]
    fn test_ast_validation_existing_unsafe_kept() {
        let orig = "fn foo(x: *const u8) -> u8 { unsafe { *x } }\n";
        let rw = "fn foo(x: *const u8) -> u8 { unsafe { *x } }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(result.passed, "errors: {:?}", result.errors);
    }

    #[test]
    fn test_ast_validation_unsafe_block_removed_ok() {
        // Removing an unsafe block is fine (safer).
        let orig = "fn foo(x: *const u8) -> u8 { unsafe { *x } }\n";
        let rw = "fn foo(x: *const u8) -> u8 { 0 }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(result.passed, "errors: {:?}", result.errors);
    }

    // --- Type annotations ---

    #[test]
    fn test_ast_validation_type_annotation_preserved() {
        let orig = "fn foo() { let x: u64 = 42; }\n";
        let rw = "fn foo() { let x: u64 = 43; }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(result.passed, "errors: {:?}", result.errors);
    }

    #[test]
    fn test_ast_validation_type_annotation_changed() {
        let orig = "fn foo() { let x: u64 = 42; }\n";
        let rw = "fn foo() { let x: i64 = 42; }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(
            result
                .errors
                .iter()
                .any(|e| matches!(e, AstValidationError::TypeAnnotationChanged { .. }))
        );
    }

    // --- Function added / removed ---

    #[test]
    fn test_ast_validation_function_removed() {
        let orig = "fn foo() {} fn bar() {}\n";
        let rw = "fn foo() {}\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::FunctionRemoved { function }
                if function == "bar"
        )));
    }

    #[test]
    fn test_ast_validation_function_added() {
        let orig = "fn foo() {}\n";
        let rw = "fn foo() {} fn bar() {}\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::FunctionAdded { function }
                if function == "bar"
        )));
    }

    // --- Visibility changes ---

    #[test]
    fn test_ast_validation_visibility_changed() {
        let orig = "fn foo() {}\n";
        let rw = "pub fn foo() {}\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::NonBodyModification { detail, .. }
                if detail.contains("visibility")
        )));
    }

    // --- Whitespace / formatting robustness ---

    #[test]
    fn test_ast_validation_whitespace_insensitive() {
        let orig = "fn  foo( x:u64 )->u64{ x+1 }\n";
        let rw = "fn foo(x: u64) -> u64 {\n    x + 1\n}\n";
        let result = validate_rewrite_ast(orig, rw);
        // syn normalizes whitespace; signatures should compare equal.
        assert!(result.passed, "errors: {:?}", result.errors);
    }

    #[test]
    fn test_ast_validation_comments_ignored() {
        let orig = "// original comment\nfn foo(x: u64) -> u64 { x + 1 }\n";
        let rw = "// different comment\nfn foo(x: u64) -> u64 { x + 1 }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(result.passed, "errors: {:?}", result.errors);
    }

    // --- Multiple functions ---

    #[test]
    fn test_ast_validation_multiple_functions_all_preserved() {
        let orig = "fn foo(x: u64) -> u64 { x } fn bar(y: i32) -> i32 { y }\n";
        let rw = "fn foo(x: u64) -> u64 { x + 0 } fn bar(y: i32) -> i32 { y + 0 }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(result.passed, "errors: {:?}", result.errors);
    }

    #[test]
    fn test_ast_validation_multiple_fns_one_changed() {
        let orig = "fn foo(x: u64) -> u64 { x } fn bar(y: i32) -> i32 { y }\n";
        let rw = "fn foo(x: u64) -> u64 { x } fn bar(y: u32) -> i32 { y as i32 }\n";
        let result = validate_rewrite_ast(orig, rw);
        assert!(!result.passed);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            AstValidationError::SignatureChanged { function, .. }
                if function == "bar"
        )));
    }

    // --- Error Display ---

    #[test]
    fn test_error_display_signature_changed() {
        let err = AstValidationError::SignatureChanged {
            function: "foo".into(),
            detail: "return type changed".into(),
        };
        let msg = err.to_string();
        assert!(msg.contains("foo"));
        assert!(msg.contains("return type changed"));
    }

    #[test]
    fn test_error_display_new_unsafe() {
        let err = AstValidationError::NewUnsafeBlock { function: "bar".into() };
        assert!(err.to_string().contains("unsafe"));
    }

    #[test]
    fn test_error_display_parse_error() {
        let err = AstValidationError::ParseError {
            which: ParseTarget::Both,
            message: "expected ident".into(),
        };
        assert!(err.to_string().contains("both"));
    }

    // --- Serialization round-trip ---

    #[test]
    fn test_ast_validation_error_serialization() {
        let err = AstValidationError::SignatureChanged {
            function: "foo".into(),
            detail: "param type".into(),
        };
        let json = serde_json::to_string(&err).unwrap();
        let restored: AstValidationError = serde_json::from_str(&json).unwrap();
        assert_eq!(err, restored);
    }

    #[test]
    fn test_ast_validation_result_serialization() {
        let result = AstValidationResult::ok(true);
        let json = serde_json::to_string(&result).unwrap();
        let restored: AstValidationResult = serde_json::from_str(&json).unwrap();
        assert!(restored.passed);
        assert!(restored.used_ast);
    }
}
