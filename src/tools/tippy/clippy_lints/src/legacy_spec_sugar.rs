use clippy_utils::diagnostics::span_lint_and_then;
use clippy_utils::source::snippet;
use clippy_utils::sym;
use rustc_ast::token::Delimiter;
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_ast::{AttrArgs, AttrItem, AttrKind, Attribute, Expr, ExprKind, Path};
use rustc_errors::Applicability;
use rustc_lint::{EarlyContext, EarlyLintPass};
use rustc_session::declare_lint_pass;
use rustc_span::Symbol;

declare_clippy_lint! {
    /// ### What it does
    /// Checks for legacy spec-surface sugars: `#[contracts::requires(..)]` /
    /// `#[contracts::ensures(..)]` attributes (any path spelling ending in
    /// `contracts::requires` / `contracts::ensures`), Kani's own contract
    /// attributes `#[kani::requires(..)]` / `#[kani::ensures(..)]`,
    /// `#[kani::proof]`, and the legacy nondet vocabulary `kani::any()` /
    /// `kani::assume()`.
    ///
    /// ### Why is this bad?
    /// Trust's direction of record (the 2026-07-09 two-language spec surface)
    /// replaces attribute contracts with first-class signature clauses
    /// (`fn f(..) requires P ensures Q { .. }`) and the legacy kani proof
    /// attribute with the native harness attribute. The attribute spellings
    /// survive only as compat desugaring and are being ripped out.
    ///
    /// ### Example
    /// ```ignore
    /// #[contracts::requires(x > 0)]
    /// fn f(x: i32) -> i32 { x }
    /// ```
    /// Use instead:
    /// ```ignore
    /// fn f(x: i32) -> i32 requires x > 0 { x }
    /// ```
    #[clippy::version = "1.97.0"]
    pub TRUST_LEGACY_SPEC_SUGAR,
    style,
    "legacy spec-surface sugar instead of Trust-native syntax"
}

declare_lint_pass!(LegacySpecSugar => [TRUST_LEGACY_SPEC_SUGAR]);

impl EarlyLintPass for LegacySpecSugar {
    fn check_attribute(&mut self, cx: &EarlyContext<'_>, attr: &Attribute) {
        // Attributes materialized by expansion (e.g. a proc-macro re-emitting
        // its input) point back at foreign code the user cannot rewrite.
        if attr.span.from_expansion() {
            return;
        }
        let AttrKind::Normal(normal) = &attr.kind else {
            return;
        };
        let item = &normal.item;

        // Any path spelling ending in `contracts::requires` / `contracts::ensures`
        // (`contracts::`, `core::contracts::`, ...) or Kani's own contract
        // attributes `kani::requires` / `kani::ensures`. Both legacy spellings
        // map to the identical first-class signature clause, so they share
        // `check_contracts_attr`. Only inert (tool-attribute) spellings reach the
        // early pass — the builtin `core::contracts::*` forms are consumed by
        // expansion first — so missing those here is expected, not a hole: they
        // are already compiler-owned compat desugarings.
        if path_ends_with(&item.path, &[sym::contracts, sym::requires])
            || path_ends_with(&item.path, &[sym::kani, sym::requires])
        {
            check_contracts_attr(cx, attr, item, "requires", "P");
        } else if path_ends_with(&item.path, &[sym::contracts, sym::ensures])
            || path_ends_with(&item.path, &[sym::kani, sym::ensures])
        {
            check_contracts_attr(cx, attr, item, "ensures", "Q");
        } else if path_ends_with(&item.path, &[sym::kani, sym::proof]) {
            // NOT `#[kani::harness]` — that is the native surface.
            span_lint_and_then(
                cx,
                TRUST_LEGACY_SPEC_SUGAR,
                attr.span,
                "legacy kani proof attribute; use `#[kani::harness]`",
                |diag| {
                    // Rename just the path so the suggestion is exact for both
                    // attribute styles and any argument list.
                    diag.span_suggestion(
                        item.path.span,
                        "use the native harness attribute",
                        "kani::harness",
                        Applicability::MachineApplicable,
                    );
                },
            );
        }
    }

    fn check_expr(&mut self, cx: &EarlyContext<'_>, expr: &Expr) {
        // Only source-written calls; a macro re-emitting `kani::any()` points at
        // foreign code the user cannot rewrite.
        if expr.span.from_expansion() {
            return;
        }
        // The nondet vocabulary appears as a bare path (`kani::any`), whether
        // called (`kani::any()`), turbofished (`kani::any::<u32>()`), or taken by
        // value. Matching the path — not the enclosing call — fires exactly once
        // and covers every form. A one-segment `any()`/`assume()` (already the
        // native spelling) has no `kani` qualifier, so it never matches.
        let ExprKind::Path(None, path) = &expr.kind else {
            return;
        };
        let (msg, native) = if path_ends_with(path, &[sym::kani, sym::any]) {
            ("legacy `kani::any()`; use the native harness `any()`", "any")
        } else if path_ends_with(path, &[sym::kani, sym::assume]) {
            ("legacy `kani::assume()`; use the native harness `assume()`", "assume")
        } else {
            return;
        };
        let Some(last) = path.segments.last() else {
            return;
        };
        span_lint_and_then(cx, TRUST_LEGACY_SPEC_SUGAR, expr.span, msg, |diag| {
            // Delete just the `kani::` qualifier (from the path start up to the
            // final segment), preserving any turbofish on the segment itself:
            // `kani::any::<u32>()` -> `any::<u32>()`.
            diag.span_suggestion(
                path.span.until(last.ident.span),
                format!("use the native harness `{native}` directly"),
                "",
                Applicability::MachineApplicable,
            );
        });
    }
}

fn check_contracts_attr(cx: &EarlyContext<'_>, attr: &Attribute, item: &AttrItem, clause: &str, placeholder: &str) {
    let (predicate, has_old_call) = match item.args.unparsed_ref() {
        Some(AttrArgs::Delimited(delim)) if !delim.tokens.is_empty() => (
            // The raw source between the delimiters, so the sketch carries the
            // user's own predicate spelling.
            snippet(cx, delim.dspan.open.between(delim.dspan.close), placeholder).to_string(),
            tokens_contain_old_call(&delim.tokens),
        ),
        _ => (placeholder.to_string(), false),
    };
    span_lint_and_then(
        cx,
        TRUST_LEGACY_SPEC_SUGAR,
        attr.span,
        "legacy contracts attribute; Trust supports first-class signature clauses",
        |diag| {
            // The predicate text moves into the signature, but legacy `ensures`
            // closure forms (`|ret| ..`) need a manual rewrite to the output
            // record + primes notation, so this is a sketch, not a fix.
            diag.span_suggestion(
                attr.span,
                "move the predicate into the signature",
                format!("fn f(..) {clause} {predicate} {{ .. }}"),
                Applicability::HasPlaceholders,
            );
            if has_old_call {
                diag.note(
                    "Trust has no `old()`: the entry state is the default; primes notation (`x'`) reads the post-state",
                );
            }
        },
    );
}

fn path_ends_with(path: &Path, suffix: &[Symbol]) -> bool {
    path.segments.len() >= suffix.len()
        && path
            .segments
            .iter()
            .rev()
            .zip(suffix.iter().rev())
            .all(|(seg, &name)| seg.ident.name == name)
}

/// Whether the (unexpanded) predicate tokens contain a call `old(..)`.
fn tokens_contain_old_call(tokens: &TokenStream) -> bool {
    let mut iter = tokens.iter().peekable();
    while let Some(tt) = iter.next() {
        match tt {
            TokenTree::Delimited(.., inner) => {
                if tokens_contain_old_call(inner) {
                    return true;
                }
            },
            TokenTree::Token(token, _) if token.is_ident_named(sym::old) => {
                if let Some(TokenTree::Delimited(_, _, Delimiter::Parenthesis, _)) = iter.peek() {
                    return true;
                }
            },
            TokenTree::Token(..) => {},
        }
    }
    false
}
