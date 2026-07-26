//! Lossless formatting support for compiler-native Trust contract clauses.
//!
//! Contract predicates are verifier-language payloads represented by source
//! spans, not Rust AST expressions. Formatting therefore preserves their
//! authored text and only normalizes the surrounding indentation. If a span
//! cannot be tied back to its expected keyword without crossing functional
//! code, the caller must abandon the enclosing rewrite.

use rustc_span::{BytePos, Pos, Span};

use crate::comment::{
    CodeCharKind, CommentCodeSlices, FindUncommented, is_last_comment_block,
    rewrite_missing_comment,
};
use crate::rewrite::{RewriteContext, RewriteError};
use crate::shape::{Indent, Shape};
use crate::utils::{mk_sp, trim_left_preserve_layout};

#[derive(Copy, Clone)]
pub(crate) struct ContractClause {
    pub(crate) keyword: &'static str,
    pub(crate) keyword_span: Option<Span>,
    pub(crate) payload: Span,
}

pub(crate) struct ContractRewrite {
    pub(crate) text: String,
    pub(crate) last_payload_hi: BytePos,
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
}

/// Returns `true` when a source gap contains no functional code.
pub(crate) fn is_comment_only_gap(snippet: &str) -> bool {
    CommentCodeSlices::new(snippet).all(|(kind, _, slice)| {
        kind == CodeCharKind::Comment || slice.chars().all(char::is_whitespace)
    })
}

fn find_contract_keyword(
    context: &RewriteContext<'_>,
    search_span: Span,
    clause: ContractClause,
) -> Result<BytePos, RewriteError> {
    if let Some(keyword_span) = clause.keyword_span {
        if keyword_span.lo() < search_span.lo()
            || keyword_span.hi() > search_span.hi()
            || context.snippet(keyword_span) != clause.keyword
            || !is_comment_only_gap(context.snippet(mk_sp(search_span.lo(), keyword_span.lo())))
        {
            return Err(RewriteError::Unknown);
        }
        return Ok(keyword_span.lo());
    }

    let snippet = context.snippet(search_span);
    let mut search_end = snippet.len();

    while let Some(index) = snippet[..search_end].find_last_uncommented(clause.keyword) {
        let before_is_boundary = snippet[..index]
            .chars()
            .next_back()
            .is_none_or(|c| !is_ident_continue(c));
        let after = index + clause.keyword.len();
        let after_is_boundary = snippet[after..]
            .chars()
            .next()
            .is_none_or(|c| !is_ident_continue(c));
        if before_is_boundary && after_is_boundary && is_comment_only_gap(&snippet[..index]) {
            return Ok(search_span.lo() + BytePos::from_usize(index));
        }
        search_end = index;
    }

    // A span-only clause that cannot be tied back to its source keyword must
    // make the enclosing rewrite fail. Manufacturing text here could drop or
    // mislabel an authored proof obligation.
    Err(RewriteError::Unknown)
}

pub(crate) fn rewrite_contract_clauses(
    context: &RewriteContext<'_>,
    clauses: Vec<ContractClause>,
    preceding_syntax_hi: BytePos,
    indent: Indent,
) -> Result<Option<ContractRewrite>, RewriteError> {
    if clauses.is_empty() {
        return Ok(None);
    }

    let clause_indent = indent.block_indent(context.config);
    let clause_shape = Shape::indented(clause_indent, context.config);
    let payload_indent = clause_indent.block_indent(context.config);
    let payload_shape = Shape::indented(payload_indent, context.config);
    let mut text = String::new();
    let mut search_lo = preceding_syntax_hi;

    for clause in clauses {
        if clause.payload.lo() <= search_lo {
            return Err(RewriteError::Unknown);
        }

        let keyword_lo =
            find_contract_keyword(context, mk_sp(search_lo, clause.payload.lo()), clause)?;

        let before_keyword_span = mk_sp(search_lo, keyword_lo);
        if !is_comment_only_gap(context.snippet(before_keyword_span)) {
            return Err(RewriteError::Unknown);
        }
        let comment_before = rewrite_missing_comment(before_keyword_span, clause_shape, context)?;
        if !comment_before.is_empty() {
            text.push_str(&clause_indent.to_string_with_newline(context.config));
            text.push_str(&comment_before);
        }

        text.push_str(&clause_indent.to_string_with_newline(context.config));
        text.push_str(clause.keyword);

        let keyword_hi = keyword_lo + BytePos::from_usize(clause.keyword.len());
        let after_keyword_span = mk_sp(keyword_hi, clause.payload.lo());
        let original_gap = context.snippet(after_keyword_span);
        if !is_comment_only_gap(original_gap) {
            return Err(RewriteError::Unknown);
        }
        let comment_after = rewrite_missing_comment(after_keyword_span, payload_shape, context)?;
        if comment_after.is_empty() {
            text.push(' ');
        } else {
            text.push(' ');
            text.push_str(&comment_after);
            if original_gap.contains('\n') || !is_last_comment_block(&comment_after) {
                text.push_str(&payload_indent.to_string_with_newline(context.config));
            } else {
                text.push(' ');
            }
        }

        let payload = context.snippet(clause.payload).trim();
        if payload.is_empty() {
            return Err(RewriteError::Unknown);
        }
        let payload = if payload.contains('\n') {
            trim_left_preserve_layout(payload, clause_indent, context.config)
                .unwrap_or_else(|| payload.to_owned())
        } else {
            payload.to_owned()
        };
        text.push_str(&payload);
        search_lo = clause.payload.hi();
    }

    Ok(Some(ContractRewrite {
        text,
        last_payload_hi: search_lo,
    }))
}

#[cfg(test)]
mod tests {
    use super::is_comment_only_gap;

    #[test]
    fn contract_gaps_reject_functional_code() {
        assert!(is_comment_only_gap("\n  // kept\n /* also kept */ \t"));
        assert!(!is_comment_only_gap("\n stray_token // comment\n"));
        assert!(!is_comment_only_gap("/* comment */ +"));
    }
}
