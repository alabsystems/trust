//! Convert `trust-strengthen::Proposal` into `SourceRewrite` with actual byte offsets.
//!
//! The key challenge: `Proposal` has `function_name` but no byte offset.
//! This module reads the source file, locates the function, and produces
//! `SourceRewrite` values with real offsets that `RewriteEngine` can apply.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::ast_rewriter::{
    AstRewriteError, AstRewriteTarget, SemanticRewrite, contract_sort_environment, resolve_target,
};
use crate::rewriter::RewriteError;
use crate::{ContractClauseKind, RewriteKind, SourceRewrite};
use trust_strengthen::{Proposal, ProposalKind};

/// Errors specific to proposal conversion.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ConvertError {
    /// The function named in the proposal was not found in the source.
    #[error("function `{name}` not found in `{file_path}`")]
    FunctionNotFound { name: String, file_path: String },
    /// The proposal's name matched multiple functions in the source file.
    #[error("function `{name}` is ambiguous in `{file_path}` ({matches} matches)")]
    AmbiguousFunction { name: String, file_path: String, matches: usize },
    /// The expression to replace was not found in the function body.
    #[error("expression `{expr}` not found in function `{name}` in `{file_path}`")]
    ExpressionNotFound { expr: String, name: String, file_path: String },
    /// The input Rust source could not be parsed structurally.
    #[error("source `{file_path}` is not parseable Rust: {error}")]
    SourceParse { file_path: String, error: String },
    /// A contract body did not survive the exact typed parser round trip.
    #[error("invalid {kind} contract for `{name}` in `{file_path}`: {error}")]
    InvalidSpec { kind: &'static str, name: String, file_path: String, error: String },
    /// A loop invariant proposal lacks a concrete loop identity/span.
    #[error(
        "cannot place loop invariant for `{name}` in `{file_path}` without an exact loop target"
    )]
    MissingLoopTarget { name: String, file_path: String },
    /// A replacement/assertion was not exactly one Rust expression or statement.
    #[error("invalid {kind} fragment for `{name}` in `{file_path}`: {error}")]
    InvalidRustFragment { kind: &'static str, name: String, file_path: String, error: String },
    /// AST target resolution failed.
    #[error("cannot resolve AST target for `{name}` in `{file_path}`: {error}")]
    AstTarget { name: String, file_path: String, error: String },
    /// Applying the resolved rewrite failed AST validation.
    #[error("rewrite for `{name}` in `{file_path}` failed AST validation: {error}")]
    InvalidRewriteResult { name: String, file_path: String, error: String },
}

impl From<ConvertError> for RewriteError {
    fn from(e: ConvertError) -> Self {
        match e {
            ConvertError::FunctionNotFound { name, file_path } => RewriteError::SourceMismatch {
                file_path,
                offset: 0,
                expected: format!("fn {name}("),
            },
            ConvertError::AmbiguousFunction { name, file_path, matches } => {
                RewriteError::AmbiguousFunction { name, file_path, matches }
            }
            ConvertError::ExpressionNotFound { expr, name: _, file_path } => {
                RewriteError::SourceMismatch { file_path, offset: 0, expected: expr }
            }
            ConvertError::SourceParse { file_path, error } => {
                RewriteError::InvalidSource { file_path, reason: error }
            }
            ConvertError::InvalidSpec { name, file_path, error, .. } => {
                RewriteError::InvalidSpec { function: name, file_path, reason: error }
            }
            ConvertError::MissingLoopTarget { name, file_path } => RewriteError::InvalidRewrite {
                function: name,
                file_path,
                reason: "loop invariant proposal has no exact loop target".to_string(),
            },
            ConvertError::InvalidRustFragment { name, file_path, error, .. }
            | ConvertError::AstTarget { name, file_path, error }
            | ConvertError::InvalidRewriteResult { name, file_path, error } => {
                RewriteError::InvalidRewrite { function: name, file_path, reason: error }
            }
        }
    }
}

/// Convert a `Proposal` into `SourceRewrite` values with real byte offsets,
/// by locating the function in the provided source text.
///
/// # Arguments
///
/// * `proposal` - The proposal from trust-strengthen.
/// * `source` - The source text of the file referenced by `proposal.function_path`.
/// * `file_path` - The actual filesystem path to the source file (used in `SourceRewrite`).
///
/// # Errors
///
/// Returns `ConvertError::FunctionNotFound` if the function cannot be located,
/// or `ConvertError::AmbiguousFunction` if the name matches multiple functions.
/// Returns `ConvertError::ExpressionNotFound` for `SafeArithmetic` if the old expression
/// is not found within the function body.
pub fn convert_proposal(
    proposal: &Proposal,
    source: &str,
    file_path: &str,
) -> Result<Vec<SourceRewrite>, ConvertError> {
    // Parse and resolve the function before inspecting the proposal payload, so
    // every path (including assertions) shares one exact identity gate.
    let sort_environment = contract_sort_environment(source, &proposal.function_name)
        .map_err(|error| ast_error(proposal, file_path, error))?;

    let semantic = match &proposal.kind {
        ProposalKind::AddPrecondition { spec_body } => contract_clause_rewrite(
            proposal,
            file_path,
            ContractClauseKind::Requires,
            spec_body,
            &sort_environment,
        )?,
        ProposalKind::AddPostcondition { spec_body } => contract_clause_rewrite(
            proposal,
            file_path,
            ContractClauseKind::Ensures,
            spec_body,
            &sort_environment,
        )?,
        ProposalKind::AddInvariant { .. } => {
            return Err(ConvertError::MissingLoopTarget {
                name: proposal.function_name.clone(),
                file_path: file_path.to_owned(),
            });
        }
        ProposalKind::SafeArithmetic { original, replacement } => {
            syn::parse_str::<syn::Expr>(replacement).map_err(|error| {
                ConvertError::InvalidRustFragment {
                    kind: "replacement expression",
                    name: proposal.function_name.clone(),
                    file_path: file_path.to_owned(),
                    error: error.to_string(),
                }
            })?;
            SemanticRewrite {
                file_path: file_path.to_owned(),
                target: AstRewriteTarget::ExpressionInFunction {
                    fn_name: proposal.function_name.clone(),
                    expr_pattern: original.clone(),
                    occurrence: 0,
                },
                kind: RewriteKind::ReplaceExpression {
                    old_text: original.clone(),
                    new_text: replacement.clone(),
                },
                function_name: proposal.function_name.clone(),
                rationale: proposal.rationale.clone(),
            }
        }
        ProposalKind::AddBoundsCheck { check_expr }
        | ProposalKind::AddNonZeroCheck { check_expr } => {
            parse_assertion(check_expr, proposal, file_path)?;
            SemanticRewrite {
                file_path: file_path.to_owned(),
                target: AstRewriteTarget::FunctionBodyStart {
                    fn_name: proposal.function_name.clone(),
                    occurrence: 0,
                },
                kind: RewriteKind::InsertAssertion { assertion: ensure_semicolon(check_expr) },
                function_name: proposal.function_name.clone(),
                rationale: proposal.rationale.clone(),
            }
        }
    };

    let resolved =
        resolve_target(source, &semantic).map_err(|error| ast_error(proposal, file_path, error))?;
    validate_resolved_rewrite(source, &resolved, proposal, file_path)?;
    Ok(vec![resolved])
}

fn contract_clause_rewrite(
    proposal: &Proposal,
    file_path: &str,
    kind: ContractClauseKind,
    spec_body: &str,
    sorts: &std::collections::BTreeMap<String, trust_types::Sort>,
) -> Result<SemanticRewrite, ConvertError> {
    let source_clause = match kind {
        ContractClauseKind::Requires => trust_types::SourceContractClause::Requires,
        ContractClauseKind::Ensures => trust_types::SourceContractClause::Ensures,
    };
    let canonical = trust_types::validate_source_spec_expr(spec_body, source_clause, sorts)
        .map_err(|error| ConvertError::InvalidSpec {
            kind: kind.keyword(),
            name: proposal.function_name.clone(),
            file_path: file_path.to_owned(),
            error: error.to_string(),
        })?;
    Ok(SemanticRewrite {
        file_path: file_path.to_owned(),
        target: AstRewriteTarget::FunctionSignatureClause {
            fn_name: proposal.function_name.clone(),
            occurrence: 0,
        },
        kind: RewriteKind::InsertContractClause { clause: kind, expression: canonical },
        function_name: proposal.function_name.clone(),
        rationale: proposal.rationale.clone(),
    })
}

fn parse_assertion(
    assertion: &str,
    proposal: &Proposal,
    file_path: &str,
) -> Result<(), ConvertError> {
    let statement = ensure_semicolon(assertion);
    syn::parse_str::<syn::Stmt>(&statement).map_err(|error| ConvertError::InvalidRustFragment {
        kind: "assertion statement",
        name: proposal.function_name.clone(),
        file_path: file_path.to_owned(),
        error: error.to_string(),
    })?;
    Ok(())
}

fn ensure_semicolon(fragment: &str) -> String {
    let trimmed = fragment.trim();
    if trimmed.ends_with(';') { trimmed.to_string() } else { format!("{trimmed};") }
}

fn ast_error(proposal: &Proposal, file_path: &str, error: AstRewriteError) -> ConvertError {
    match error {
        AstRewriteError::FunctionNotFound { .. } => ConvertError::FunctionNotFound {
            name: proposal.function_name.clone(),
            file_path: file_path.to_owned(),
        },
        AstRewriteError::AmbiguousFunction { matches, .. } => ConvertError::AmbiguousFunction {
            name: proposal.function_name.clone(),
            file_path: file_path.to_owned(),
            matches,
        },
        AstRewriteError::ExpressionNotFound { pattern, .. } => ConvertError::ExpressionNotFound {
            expr: pattern,
            name: proposal.function_name.clone(),
            file_path: file_path.to_owned(),
        },
        AstRewriteError::SourceParseError(error) => {
            ConvertError::SourceParse { file_path: file_path.to_owned(), error }
        }
        other => ConvertError::AstTarget {
            name: proposal.function_name.clone(),
            file_path: file_path.to_owned(),
            error: other.to_string(),
        },
    }
}

fn validate_resolved_rewrite(
    source: &str,
    rewrite: &SourceRewrite,
    proposal: &Proposal,
    file_path: &str,
) -> Result<(), ConvertError> {
    let rewritten =
        crate::RewriteEngine::new().apply_rewrite(source, rewrite).map_err(|error| {
            ConvertError::InvalidRewriteResult {
                name: proposal.function_name.clone(),
                file_path: file_path.to_owned(),
                error: error.to_string(),
            }
        })?;
    let validation = crate::validate_rewrite_ast(source, &rewritten);
    if !validation.used_ast || !validation.passed {
        return Err(ConvertError::InvalidRewriteResult {
            name: proposal.function_name.clone(),
            file_path: file_path.to_owned(),
            error: format!("{:?}", validation.errors),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_strengthen::{Proposal, ProposalKind};

    fn make_source() -> &'static str {
        "pub fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n"
    }

    fn make_proposal(kind: ProposalKind) -> Proposal {
        Proposal {
            function_path: "crate::get_midpoint".into(),
            function_name: "get_midpoint".into(),
            kind,
            confidence: 0.9,
            rationale: "overflow protection".into(),
        }
    }

    #[test]
    fn test_convert_precondition() {
        let source = make_source();
        let proposal = make_proposal(ProposalKind::AddPrecondition {
            spec_body: "a + b < 18446744073709551615".into(),
        });
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        assert_eq!(&source[rewrites[0].offset..rewrites[0].offset + 1], "{");
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertContractClause {
                clause: ContractClauseKind::Requires,
                expression,
            } if expression == "a + b < 18446744073709551615"
        ));
    }

    #[test]
    fn test_convert_postcondition() {
        let source = make_source();
        let proposal = make_proposal(ProposalKind::AddPostcondition {
            spec_body: "result <= a && result <= b".into(),
        });
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertContractClause {
                clause: ContractClauseKind::Ensures,
                expression,
            } if expression == "result <= a && result <= b"
        ));
    }

    #[test]
    fn test_convert_safe_arithmetic() {
        let source = make_source();
        let proposal = make_proposal(ProposalKind::SafeArithmetic {
            original: "a + b".into(),
            replacement: "a.checked_add(b).expect(\"overflow\")".into(),
        });
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        // The offset should point to where "a + b" appears in the function body
        let offset = rewrites[0].offset;
        assert_eq!(&source[offset..offset + 5], "a + b");
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::ReplaceExpression { old_text, new_text }
                if old_text == "a + b" && new_text.contains("checked_add")
        ));
    }

    #[test]
    fn test_convert_bounds_check() {
        let source = "fn index_into(v: &[u8], i: usize) -> u8 {\n    v[i]\n}\n";
        let proposal = Proposal {
            function_path: "crate::index_into".into(),
            function_name: "index_into".into(),
            kind: ProposalKind::AddBoundsCheck { check_expr: "assert!(i < v.len());".into() },
            confidence: 0.85,
            rationale: "bounds check".into(),
        };
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAssertion { assertion } if assertion.contains("assert!")
        ));
    }

    #[test]
    fn test_convert_non_zero_check() {
        let source = "fn divide(a: u64, b: u64) -> u64 {\n    a / b\n}\n";
        let proposal = Proposal {
            function_path: "crate::divide".into(),
            function_name: "divide".into(),
            kind: ProposalKind::AddNonZeroCheck {
                check_expr: "assert!(b != 0, \"division by zero\");".into(),
            },
            confidence: 0.95,
            rationale: "prevent division by zero".into(),
        };
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        assert!(matches!(
            &rewrites[0].kind,
            RewriteKind::InsertAssertion { assertion } if assertion.contains("!= 0")
        ));
    }

    #[test]
    fn test_convert_function_not_found() {
        let source = "fn foo() {}\n";
        let proposal = make_proposal(ProposalKind::AddPrecondition { spec_body: "true".into() });
        let result = convert_proposal(&proposal, source, "src/lib.rs");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ConvertError::FunctionNotFound { .. }));
    }

    #[test]
    fn test_convert_ambiguous_function_fails_closed() {
        let source = "mod left { fn get_midpoint() {} }\nmod right { fn get_midpoint() {} }\n";
        let proposal = make_proposal(ProposalKind::AddPrecondition { spec_body: "true".into() });

        let error = convert_proposal(&proposal, source, "src/lib.rs").unwrap_err();

        assert!(matches!(
            error,
            ConvertError::AmbiguousFunction { name, matches: 2, .. }
                if name == "get_midpoint"
        ));
    }

    #[test]
    fn test_convert_expression_not_found() {
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n";
        let proposal = make_proposal(ProposalKind::SafeArithmetic {
            original: "x * y".into(),
            replacement: "x.checked_mul(y).unwrap()".into(),
        });
        let result = convert_proposal(&proposal, source, "src/lib.rs");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ConvertError::ExpressionNotFound { .. }));
    }

    #[test]
    fn test_convert_indented_function() {
        let source = "impl Calculator {\n    pub fn add(&self, a: u64, b: u64) -> u64 {\n        a + b\n    }\n}\n";
        let proposal = Proposal {
            function_path: "crate::Calculator::add".into(),
            function_name: "add".into(),
            kind: ProposalKind::AddPrecondition {
                spec_body: "a + b < 18446744073709551615".into(),
            },
            confidence: 0.9,
            rationale: "overflow".into(),
        };
        let rewrites = convert_proposal(&proposal, source, "src/lib.rs").unwrap();
        assert_eq!(rewrites.len(), 1);
        let rewritten = crate::RewriteEngine::new().apply_rewrite(source, &rewrites[0]).unwrap();
        assert!(rewritten.contains("        requires a + b < 18446744073709551615"));
    }

    #[test]
    fn test_convert_error_into_rewrite_error() {
        let err = ConvertError::FunctionNotFound { name: "foo".into(), file_path: "bar.rs".into() };
        let rewrite_err: RewriteError = err.into();
        assert!(matches!(rewrite_err, RewriteError::SourceMismatch { .. }));
    }

    #[test]
    fn test_convert_invariant() {
        let source = make_source();
        let proposal = make_proposal(ProposalKind::AddInvariant { spec_body: "a <= b".into() });
        assert!(matches!(
            convert_proposal(&proposal, source, "src/lib.rs"),
            Err(ConvertError::MissingLoopTarget { .. })
        ));
    }

    #[test]
    fn invalid_english_or_injected_contract_never_reaches_a_rewrite() {
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 { a + b }";
        for spec_body in ["caller must ensure: a > 0", "a > 0); fn injected() {"] {
            let proposal =
                make_proposal(ProposalKind::AddPrecondition { spec_body: spec_body.into() });
            assert!(matches!(
                convert_proposal(&proposal, source, "src/lib.rs"),
                Err(ConvertError::InvalidSpec { .. })
            ));
        }
    }

    #[test]
    fn expression_search_is_bounded_to_selected_function() {
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 { a - b }\nfn later(a: u64, b: u64) -> u64 { a + b }\n";
        let proposal = make_proposal(ProposalKind::SafeArithmetic {
            original: "a + b".into(),
            replacement: "a.checked_add(b).unwrap()".into(),
        });
        assert!(matches!(
            convert_proposal(&proposal, source, "src/lib.rs"),
            Err(ConvertError::ExpressionNotFound { .. })
        ));
    }

    #[test]
    fn two_impl_methods_require_qualified_identity() {
        let source = "struct A; struct B; impl A { fn run(&self) {} } impl B { fn run(&self) {} }";
        let mut proposal = Proposal {
            function_path: "src/lib.rs".into(),
            function_name: "run".into(),
            kind: ProposalKind::AddPrecondition { spec_body: "true".into() },
            confidence: 1.0,
            rationale: "test".into(),
        };
        assert!(matches!(
            convert_proposal(&proposal, source, "src/lib.rs"),
            Err(ConvertError::AmbiguousFunction { matches: 2, .. })
        ));
        proposal.function_name = "B::run".into();
        let rewrite = convert_proposal(&proposal, source, "src/lib.rs").unwrap().remove(0);
        let rewritten = crate::RewriteEngine::new().apply_rewrite(source, &rewrite).unwrap();
        let b_impl = rewritten.find("impl B").unwrap();
        assert!(rewritten[b_impl..].contains("requires true"));
    }

    #[test]
    fn bool_contract_uses_signature_sort_and_reparses() {
        let source = "fn get_midpoint(flag: bool) -> bool { flag }";
        let proposal =
            make_proposal(ProposalKind::AddPrecondition { spec_body: "flag == true".into() });
        let rewrite = convert_proposal(&proposal, source, "src/lib.rs").unwrap().remove(0);
        let RewriteKind::InsertContractClause {
            clause: ContractClauseKind::Requires,
            expression: body,
        } = &rewrite.kind
        else {
            unreachable!()
        };
        let mut sorts = std::collections::BTreeMap::new();
        sorts.insert("flag".to_string(), trust_types::Sort::Bool);
        assert!(trust_types::canonicalize_spec_expr_with_sorts(body, &sorts).is_ok());
    }

    #[test]
    fn inserts_before_where_and_preserves_multiline_signature() {
        let source = "fn bounded<T>(\n    value: T,\n) -> T\nwhere\n    T: Copy,\n{ value }\n";
        let proposal = Proposal {
            function_path: "crate::bounded".into(),
            function_name: "bounded".into(),
            kind: ProposalKind::AddPrecondition { spec_body: "true".into() },
            confidence: 1.0,
            rationale: "test".into(),
        };
        let rewrite = convert_proposal(&proposal, source, "src/lib.rs").unwrap().remove(0);
        assert!(source[rewrite.offset..].starts_with("where"));
        let rewritten = crate::RewriteEngine::new().apply_rewrite(source, &rewrite).unwrap();
        assert!(rewritten.contains(") -> T\n    requires true\nwhere"));
        assert!(crate::validate_rewrite_ast(source, &rewritten).passed);
    }

    #[test]
    fn existing_native_clauses_are_masked_for_a_second_rewrite() {
        let source = "fn bounded(value: i32) -> i32\n    requires value >= 0\n{ value }\n";
        let proposal = Proposal {
            function_path: "crate::bounded".into(),
            function_name: "bounded".into(),
            kind: ProposalKind::AddPostcondition { spec_body: "result >= value".into() },
            confidence: 1.0,
            rationale: "test".into(),
        };
        let rewrite = convert_proposal(&proposal, source, "src/lib.rs").unwrap().remove(0);
        let rewritten = crate::RewriteEngine::new().apply_rewrite(source, &rewrite).unwrap();
        assert!(rewritten.contains("requires value >= 0\n    ensures result >= value\n{"));
        assert!(crate::validate_rewrite_ast(source, &rewritten).passed);
    }

    #[test]
    fn compatibility_only_expression_syntax_is_never_generated() {
        let source = "fn bounded(value: i32) -> i32 { value }";
        for body in ["old(value) >= 0", "forall |i| i >= 0"] {
            let proposal = make_proposal(ProposalKind::AddPostcondition { spec_body: body.into() });
            assert!(convert_proposal(&proposal, source, "src/lib.rs").is_err());
        }
    }
}
