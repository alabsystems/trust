//! Source-level rewrite engine.
//!
//! Applies a `RewritePlan` to source files: inserting native signature clauses,
//! replacing expressions, and inserting assertions. Operates on raw source text
//! to avoid requiring a full parse tree.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{RewriteKind, RewritePlan, SourceRewrite};

/// Errors that can occur during source rewriting.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum RewriteError {
    /// A governance rule was violated.
    #[error("governance violation in `{function}`: {violations:?}")]
    Governance { function: String, violations: Vec<crate::GovernanceViolation> },
    /// A proposal did not carry provenance strong enough for source rewriting.
    #[error("unsafe rewrite provenance for `{function}`: {reason}")]
    UnsafeProvenance { function: String, reason: String },
    /// The source text did not contain the expected content at the rewrite site.
    #[error("source mismatch at offset {offset} in `{file_path}`: expected `{expected}`")]
    SourceMismatch { file_path: String, offset: usize, expected: String },
    /// A name-only proposal matched multiple functions in one source file.
    #[error("function `{name}` is ambiguous in `{file_path}` ({matches} matches)")]
    AmbiguousFunction { name: String, file_path: String, matches: usize },
    /// The source file itself was not valid Rust for structural planning.
    #[error("invalid Rust source `{file_path}`: {reason}")]
    InvalidSource { file_path: String, reason: String },
    /// A contract string failed the typed parser round trip.
    #[error("invalid contract for `{function}` in `{file_path}`: {reason}")]
    InvalidSpec { function: String, file_path: String, reason: String },
    /// A semantic target or produced rewrite was invalid.
    #[error("invalid rewrite for `{function}` in `{file_path}`: {reason}")]
    InvalidRewrite { function: String, file_path: String, reason: String },
    /// A fixed-offset rewrite was not bound to the source revision it targets.
    #[error("rewrite plan for `{file_path}` has no source-content binding")]
    UnboundPlan { file_path: String },
    /// The source changed after the semantic target was resolved.
    #[error("stale rewrite plan for `{file_path}`: expected source hash {expected}, got {actual}")]
    StalePlan { file_path: String, expected: String, actual: String },
    /// The offset is out of bounds for the source text.
    #[error("offset {offset} out of bounds for `{file_path}` (length {length})")]
    OffsetOutOfBounds { file_path: String, offset: usize, length: usize },
    /// A byte offset split a UTF-8 scalar value.
    #[error("offset {offset} is not a UTF-8 character boundary in `{file_path}`")]
    OffsetNotCharBoundary { file_path: String, offset: usize },
    /// Two fixed-source edits cannot be composed without changing their meaning.
    #[error(
        "conflicting rewrites in `{file_path}` at offsets {first_offset} and {second_offset}: {reason}"
    )]
    ConflictingRewrites {
        file_path: String,
        first_offset: usize,
        second_offset: usize,
        reason: String,
    },
}

/// Engine that applies rewrite plans to source text.
///
/// The engine works on in-memory source strings. File I/O is the caller's
/// responsibility -- this keeps the engine testable and side-effect free.
#[derive(Debug)]
pub struct RewriteEngine {
    /// The current indentation string to use for inserted lines.
    pub(crate) indent: String,
}

impl Default for RewriteEngine {
    fn default() -> Self {
        Self { indent: "    ".into() }
    }
}

impl RewriteEngine {
    /// Create a new rewrite engine with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a rewrite engine with custom indentation.
    #[must_use]
    pub fn with_indent(indent: impl Into<String>) -> Self {
        Self { indent: indent.into() }
    }

    /// Apply a single rewrite to source text, returning the modified text.
    ///
    /// # Errors
    ///
    /// Returns `RewriteError::OffsetOutOfBounds` if the offset exceeds the source length.
    /// Returns `RewriteError::SourceMismatch` for `ReplaceExpression` when the old text
    /// is not found at the specified offset.
    pub fn apply_rewrite(
        &self,
        source: &str,
        rewrite: &SourceRewrite,
    ) -> Result<String, RewriteError> {
        if let Some(expected) = &rewrite.expected_source_hash {
            let actual = trust_types::stable_sha256_hex(source.as_bytes());
            if &actual != expected {
                return Err(RewriteError::StalePlan {
                    file_path: rewrite.file_path.clone(),
                    expected: expected.clone(),
                    actual,
                });
            }
        }
        self.apply_rewrite_after_binding(source, rewrite)
    }

    fn apply_rewrite_after_binding(
        &self,
        source: &str,
        rewrite: &SourceRewrite,
    ) -> Result<String, RewriteError> {
        if let Some(reason) = crate::report_only_provenance_path_reason(&rewrite.file_path) {
            return Err(RewriteError::UnsafeProvenance {
                function: rewrite.function_name.clone(),
                reason: reason.into(),
            });
        }

        if rewrite.offset > source.len() {
            return Err(RewriteError::OffsetOutOfBounds {
                file_path: rewrite.file_path.clone(),
                offset: rewrite.offset,
                length: source.len(),
            });
        }
        if !source.is_char_boundary(rewrite.offset) {
            return Err(RewriteError::OffsetNotCharBoundary {
                file_path: rewrite.file_path.clone(),
                offset: rewrite.offset,
            });
        }

        match &rewrite.kind {
            RewriteKind::InsertAttribute { attribute } => {
                let line_start = source[..rewrite.offset].rfind('\n').map_or(0, |index| index + 1);
                let before = &source[line_start..rewrite.offset];
                let indent: String = if before.is_empty() {
                    source[rewrite.offset..]
                        .chars()
                        .take_while(|character| *character == ' ' || *character == '\t')
                        .collect()
                } else {
                    before
                        .chars()
                        .take_while(|character| *character == ' ' || *character == '\t')
                        .collect()
                };
                let attribute = if indent.is_empty() || attribute.starts_with(&indent) {
                    attribute.clone()
                } else {
                    format!("{indent}{attribute}")
                };
                Ok(self.insert_at(source, rewrite.offset, &format!("{attribute}\n")))
            }
            RewriteKind::InsertContractClause { clause, expression } => {
                let source_clause = match clause {
                    crate::ContractClauseKind::Requires => {
                        trust_types::SourceContractClause::Requires
                    }
                    crate::ContractClauseKind::Ensures => {
                        trust_types::SourceContractClause::Ensures
                    }
                };
                if expression.contains("old(")
                    || expression.contains("old (")
                    || expression.contains("forall |")
                    || expression.contains("exists |")
                {
                    return Err(RewriteError::InvalidSpec {
                        function: rewrite.function_name.clone(),
                        file_path: rewrite.file_path.clone(),
                        reason: "compatibility-only old()/closure quantifier syntax cannot be generated as a native clause".to_string(),
                    });
                }
                let sorts =
                    crate::ast_rewriter::contract_sort_environment(source, &rewrite.function_name)
                        .map_err(|error| RewriteError::InvalidSpec {
                            function: rewrite.function_name.clone(),
                            file_path: rewrite.file_path.clone(),
                            reason: error.to_string(),
                        })?;
                let expression =
                    trust_types::validate_source_spec_expr(expression, source_clause, &sorts)
                        .map_err(|error| RewriteError::InvalidSpec {
                            function: rewrite.function_name.clone(),
                            file_path: rewrite.file_path.clone(),
                            reason: error.to_string(),
                        })?;
                Ok(self.insert_at(
                    source,
                    rewrite.offset,
                    &self.format_contract_clause_insertion(
                        source,
                        rewrite.offset,
                        clause.keyword(),
                        &expression,
                    ),
                ))
            }
            RewriteKind::ReplaceExpression { old_text, new_text } => {
                self.replace_at(source, rewrite, old_text, new_text)
            }
            RewriteKind::InsertAssertion { assertion } => Ok(self.insert_at(
                source,
                rewrite.offset,
                &self.format_assertion_insertion(source, rewrite.offset, assertion),
            )),
        }
    }

    /// Apply all rewrites in a plan to a single source string.
    ///
    /// The plan MUST be sorted (via `sort_for_application`) with descending offsets
    /// so that earlier rewrites do not invalidate later offsets.
    ///
    /// # Errors
    ///
    /// Returns the first `RewriteError` encountered.
    pub fn apply_plan_to_source(
        &self,
        source: &str,
        plan: &RewritePlan,
    ) -> Result<String, RewriteError> {
        let actual = trust_types::stable_sha256_hex(source.as_bytes());
        for rewrite in &plan.rewrites {
            if let Some(expected) = &rewrite.expected_source_hash
                && expected != &actual
            {
                return Err(RewriteError::StalePlan {
                    file_path: rewrite.file_path.clone(),
                    expected: expected.clone(),
                    actual,
                });
            }
        }
        validate_rewrite_set(source, &plan.rewrites)?;
        let mut rewrites = plan.rewrites.iter().collect::<Vec<_>>();
        rewrites.sort_by(|left, right| rewrite_application_order(left, right));

        let mut result = source.to_owned();
        for rewrite in rewrites {
            result = self.apply_rewrite_after_binding(&result, rewrite)?;
        }
        Ok(result)
    }

    fn format_assertion_insertion(&self, source: &str, offset: usize, assertion: &str) -> String {
        let before = &source[..offset];
        let after = &source[offset..];
        if before.ends_with('{') {
            let line_start = before.rfind('\n').map_or(0, |index| index + 1);
            let base_indent: String = source[line_start..]
                .chars()
                .take_while(|character| *character == ' ' || *character == '\t')
                .collect();
            let body_indent = format!("{base_indent}{}", self.indent);
            if after.starts_with("\r\n") || after.starts_with('\n') {
                format!("\n{body_indent}{assertion}")
            } else if after.starts_with('}') {
                format!("\n{body_indent}{assertion}\n{base_indent}")
            } else {
                format!("\n{body_indent}{assertion}\n{body_indent}")
            }
        } else {
            format!("{}{assertion}\n", self.indent)
        }
    }

    fn format_contract_clause_insertion(
        &self,
        source: &str,
        offset: usize,
        keyword: &str,
        expression: &str,
    ) -> String {
        let line_start = source[..offset].rfind('\n').map_or(0, |index| index + 1);
        let line_prefix = &source[line_start..offset];
        let base_indent: String = source[line_start..]
            .chars()
            .take_while(|character| *character == ' ' || *character == '\t')
            .collect();
        let clause_indent = format!("{base_indent}{}", self.indent);
        let first_indent =
            if line_prefix.trim().is_empty() { self.indent.as_str() } else { &clause_indent };
        let mut expression_lines = expression.trim().lines();
        let first = expression_lines.next().unwrap_or_default().trim();
        let mut clause_text = format!("{first_indent}{keyword} {first}");
        for line in expression_lines {
            clause_text.push('\n');
            clause_text.push_str(&clause_indent);
            clause_text.push_str(&self.indent);
            clause_text.push_str(line.trim());
        }
        let leading_newline = if line_prefix.trim().is_empty() { "" } else { "\n" };
        format!("{leading_newline}{clause_text}\n{base_indent}")
    }

    /// Insert text at a byte offset.
    fn insert_at(&self, source: &str, offset: usize, text: &str) -> String {
        let mut result = String::with_capacity(source.len() + text.len());
        result.push_str(&source[..offset]);
        result.push_str(text);
        result.push_str(&source[offset..]);
        result
    }

    /// Replace text at a byte offset.
    fn replace_at(
        &self,
        source: &str,
        rewrite: &SourceRewrite,
        old_text: &str,
        new_text: &str,
    ) -> Result<String, RewriteError> {
        let Some(end) = rewrite.offset.checked_add(old_text.len()) else {
            return Err(RewriteError::OffsetOutOfBounds {
                file_path: rewrite.file_path.clone(),
                offset: rewrite.offset,
                length: source.len(),
            });
        };
        if !source.is_char_boundary(end) {
            return Err(RewriteError::OffsetNotCharBoundary {
                file_path: rewrite.file_path.clone(),
                offset: end,
            });
        }
        if end > source.len() || &source[rewrite.offset..end] != old_text {
            return Err(RewriteError::SourceMismatch {
                file_path: rewrite.file_path.clone(),
                offset: rewrite.offset,
                expected: old_text.into(),
            });
        }

        let mut result = String::with_capacity(source.len() - old_text.len() + new_text.len());
        result.push_str(&source[..rewrite.offset]);
        result.push_str(new_text);
        result.push_str(&source[end..]);
        Ok(result)
    }
}

fn insertion_text(rewrite: &SourceRewrite) -> Option<&str> {
    match &rewrite.kind {
        RewriteKind::InsertAttribute { attribute } => Some(attribute),
        RewriteKind::InsertContractClause { expression, .. } => Some(expression),
        RewriteKind::InsertAssertion { assertion } => Some(assertion),
        RewriteKind::ReplaceExpression { .. } => None,
    }
}

fn rewrite_application_order(left: &SourceRewrite, right: &SourceRewrite) -> std::cmp::Ordering {
    right.offset.cmp(&left.offset).then_with(|| match (&left.kind, &right.kind) {
        // At a shared start, replacement must consume the original source
        // before an insertion changes that byte position.
        (RewriteKind::ReplaceExpression { .. }, RewriteKind::ReplaceExpression { .. }) => {
            std::cmp::Ordering::Equal
        }
        (RewriteKind::ReplaceExpression { .. }, _) => std::cmp::Ordering::Less,
        (_, RewriteKind::ReplaceExpression { .. }) => std::cmp::Ordering::Greater,
        _ => insertion_text(right).cmp(&insertion_text(left)),
    })
}

fn validate_rewrite_set(source: &str, rewrites: &[SourceRewrite]) -> Result<(), RewriteError> {
    for rewrite in rewrites {
        if rewrite.offset > source.len() {
            return Err(RewriteError::OffsetOutOfBounds {
                file_path: rewrite.file_path.clone(),
                offset: rewrite.offset,
                length: source.len(),
            });
        }
        if !source.is_char_boundary(rewrite.offset) {
            return Err(RewriteError::OffsetNotCharBoundary {
                file_path: rewrite.file_path.clone(),
                offset: rewrite.offset,
            });
        }
    }

    for (index, left) in rewrites.iter().enumerate() {
        let left_end = match &left.kind {
            RewriteKind::ReplaceExpression { old_text, .. } => left
                .offset
                .checked_add(old_text.len())
                .filter(|end| *end <= source.len() && source.is_char_boundary(*end))
                .ok_or_else(|| RewriteError::OffsetOutOfBounds {
                    file_path: left.file_path.clone(),
                    offset: left.offset,
                    length: source.len(),
                })?,
            _ => left.offset,
        };
        for right in &rewrites[index + 1..] {
            if left.file_path != right.file_path {
                continue;
            }
            let right_end = match &right.kind {
                RewriteKind::ReplaceExpression { old_text, .. } => right
                    .offset
                    .checked_add(old_text.len())
                    .filter(|end| *end <= source.len() && source.is_char_boundary(*end))
                    .ok_or_else(|| RewriteError::OffsetOutOfBounds {
                        file_path: right.file_path.clone(),
                        offset: right.offset,
                        length: source.len(),
                    })?,
                _ => right.offset,
            };

            let left_replaces = left_end > left.offset;
            let right_replaces = right_end > right.offset;
            let overlaps = if left_replaces && right_replaces {
                left.offset < right_end && right.offset < left_end
            } else if left_replaces {
                left.offset < right.offset && right.offset < left_end
            } else if right_replaces {
                right.offset < left.offset && left.offset < right_end
            } else {
                false
            };
            let duplicate_insertion = !left_replaces
                && !right_replaces
                && left.offset == right.offset
                && left.kind == right.kind;
            if overlaps || duplicate_insertion {
                return Err(RewriteError::ConflictingRewrites {
                    file_path: left.file_path.clone(),
                    first_offset: left.offset,
                    second_offset: right.offset,
                    reason: if duplicate_insertion {
                        "duplicate insertion".to_string()
                    } else {
                        "overlapping replacement range".to_string()
                    },
                });
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ClaimProvenance, RewriteKind, SourceRewrite};

    fn make_rewrite(offset: usize, kind: RewriteKind) -> SourceRewrite {
        SourceRewrite {
            file_path: "test.rs".into(),
            offset,
            kind,
            function_name: "test_fn".into(),
            rationale: "test".into(),
            expected_source_hash: None,
            provenance: ClaimProvenance::Authoritative,
        }
    }

    #[test]
    fn test_insert_attribute_at_start() {
        let engine = RewriteEngine::new();
        let source = "fn foo() {}\n";
        let rewrite = make_rewrite(
            0,
            RewriteKind::InsertAttribute { attribute: "#[requires(\"x > 0\")]".into() },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert_eq!(result, "#[requires(\"x > 0\")]\nfn foo() {}\n");
    }

    #[test]
    fn test_insert_attribute_at_offset() {
        let engine = RewriteEngine::new();
        let source = "// comment\nfn foo() {}\n";
        let rewrite = make_rewrite(
            11, // after "// comment\n"
            RewriteKind::InsertAttribute { attribute: "#[ensures(\"result >= 0\")]".into() },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert!(result.contains("#[ensures(\"result >= 0\")]"));
        assert!(result.starts_with("// comment\n"));
    }

    #[test]
    fn test_replace_expression() {
        let engine = RewriteEngine::new();
        let source = "let x = a + b;\n";
        let rewrite = make_rewrite(
            8, // offset of "a + b"
            RewriteKind::ReplaceExpression {
                old_text: "a + b".into(),
                new_text: "a.checked_add(b).unwrap()".into(),
            },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert_eq!(result, "let x = a.checked_add(b).unwrap();\n");
    }

    #[test]
    fn test_replace_expression_mismatch() {
        let engine = RewriteEngine::new();
        let source = "let x = a + b;\n";
        let rewrite = make_rewrite(
            8,
            RewriteKind::ReplaceExpression {
                old_text: "a * b".into(),
                new_text: "a.checked_mul(b).unwrap()".into(),
            },
        );

        let result = engine.apply_rewrite(source, &rewrite);
        assert!(result.is_err());
        assert!(matches!(result, Err(RewriteError::SourceMismatch { .. })));
    }

    #[test]
    fn test_insert_assertion() {
        let engine = RewriteEngine::new();
        let source = "    let x = v[i];\n";
        let rewrite = make_rewrite(
            0,
            RewriteKind::InsertAssertion {
                assertion: "assert!(i < v.len(), \"index out of bounds\");".into(),
            },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert!(result.starts_with("    assert!(i < v.len()"));
        assert!(result.contains("let x = v[i]"));
    }

    #[test]
    fn test_offset_out_of_bounds() {
        let engine = RewriteEngine::new();
        let source = "short";
        let rewrite = make_rewrite(
            100,
            RewriteKind::InsertAttribute { attribute: "#[requires(\"true\")]".into() },
        );

        let result = engine.apply_rewrite(source, &rewrite);
        assert!(result.is_err());
        assert!(matches!(result, Err(RewriteError::OffsetOutOfBounds { .. })));
    }

    #[test]
    fn utf8_mid_scalar_offset_is_rejected_without_panicking() {
        let engine = RewriteEngine::new();
        let source = "πfn foo() {}";
        let rewrite = make_rewrite(
            1,
            RewriteKind::InsertAttribute { attribute: "#[trust::requires(true)]".into() },
        );
        assert!(matches!(
            engine.apply_rewrite(source, &rewrite),
            Err(RewriteError::OffsetNotCharBoundary { offset: 1, .. })
        ));
    }

    #[test]
    fn overlapping_replacements_fail_closed_before_application() {
        let engine = RewriteEngine::new();
        let source = "abcdef";
        let plan = RewritePlan {
            rewrites: vec![
                make_rewrite(
                    1,
                    RewriteKind::ReplaceExpression { old_text: "bcd".into(), new_text: "x".into() },
                ),
                make_rewrite(
                    3,
                    RewriteKind::ReplaceExpression { old_text: "de".into(), new_text: "y".into() },
                ),
            ],
            summary: "overlap".into(),
        };
        assert!(matches!(
            engine.apply_plan_to_source(source, &plan),
            Err(RewriteError::ConflictingRewrites { .. })
        ));
    }

    #[test]
    fn shared_start_replacement_then_insertion_is_deterministic() {
        let engine = RewriteEngine::new();
        let source = "fn f() {}";
        let plan = RewritePlan {
            // Deliberately put the insertion first. The engine owns the safe
            // same-offset order rather than trusting caller sort stability.
            rewrites: vec![
                make_rewrite(0, RewriteKind::InsertAttribute { attribute: "#[inline]".into() }),
                make_rewrite(
                    0,
                    RewriteKind::ReplaceExpression {
                        old_text: "fn f".into(),
                        new_text: "fn g".into(),
                    },
                ),
            ],
            summary: "shared start".into(),
        };
        assert_eq!(engine.apply_plan_to_source(source, &plan).unwrap(), "#[inline]\nfn g() {}");
    }

    #[test]
    fn duplicate_insertions_are_rejected() {
        let engine = RewriteEngine::new();
        let source = "fn f() {}";
        let rewrite =
            make_rewrite(0, RewriteKind::InsertAttribute { attribute: "#[inline]".into() });
        let plan =
            RewritePlan { rewrites: vec![rewrite.clone(), rewrite], summary: "duplicate".into() };
        assert!(matches!(
            engine.apply_plan_to_source(source, &plan),
            Err(RewriteError::ConflictingRewrites { .. })
        ));
    }

    #[test]
    fn test_rejects_binary_pseudo_path_before_applying_rewrite() {
        let engine = RewriteEngine::new();
        let source = "fn recovered(arg0: u64) -> u64 { arg0 }\n";
        let mut rewrite = make_rewrite(
            0,
            RewriteKind::InsertAttribute { attribute: "#[requires(\"arg0 != 0\")]".into() },
        );
        rewrite.file_path = "binary:0x401000".into();
        rewrite.function_name = "recovered".into();

        let result = engine.apply_rewrite(source, &rewrite);

        assert!(matches!(
            result,
            Err(RewriteError::UnsafeProvenance { function, reason })
                if function == "recovered"
                    && reason.contains("binary pseudo-paths")
                    && reason.contains("cannot be rewritten")
        ));
    }

    #[test]
    fn test_apply_plan_multiple_rewrites() {
        let engine = RewriteEngine::new();
        let source = "fn foo(a: u64, b: u64) -> u64 {\n    a + b\n}\n";

        let mut plan = crate::RewritePlan::new("test plan");
        // Insert attribute at start (offset 0)
        plan.rewrites.push(make_rewrite(
            0,
            RewriteKind::InsertAttribute { attribute: "#[requires(\"a + b < u64::MAX\")]".into() },
        ));
        plan.sort_for_application();

        let result = engine.apply_plan_to_source(source, &plan).unwrap();
        assert!(result.starts_with("#[requires(\"a + b < u64::MAX\")]"));
        assert!(result.contains("fn foo"));
    }

    #[test]
    fn test_apply_plan_empty() {
        let engine = RewriteEngine::new();
        let source = "fn foo() {}\n";
        let plan = crate::RewritePlan::new("empty plan");
        let result = engine.apply_plan_to_source(source, &plan).unwrap();
        assert_eq!(result, source);
    }

    #[test]
    fn test_custom_indent() {
        let engine = RewriteEngine::with_indent("\t");
        let source = "let x = 1;\n";
        let rewrite =
            make_rewrite(0, RewriteKind::InsertAssertion { assertion: "assert!(x > 0);".into() });

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert!(result.starts_with("\tassert!(x > 0);"));
    }

    #[test]
    fn test_replace_at_end_of_source() {
        let engine = RewriteEngine::new();
        let source = "a + b";
        let rewrite = make_rewrite(
            0,
            RewriteKind::ReplaceExpression {
                old_text: "a + b".into(),
                new_text: "a.wrapping_add(b)".into(),
            },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert_eq!(result, "a.wrapping_add(b)");
    }

    #[test]
    fn test_insert_at_end_of_source() {
        let engine = RewriteEngine::new();
        let source = "fn foo() {}";
        let rewrite = make_rewrite(
            source.len(),
            RewriteKind::InsertAttribute { attribute: "\n// end".into() },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert!(result.ends_with("\n// end\n"));
    }
}
