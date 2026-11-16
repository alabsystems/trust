use rustc_ast::token;
use rustc_ast::tokenstream::{DelimSpacing, DelimSpan, Spacing, TokenStream, TokenTree};
use rustc_errors::ErrorGuaranteed;
use rustc_expand::base::{AttrProcMacro, ExtCtxt};
use rustc_span::Span;
use rustc_span::symbol::{Ident, Symbol, kw, sym};

pub(crate) struct ExpandRequires;

pub(crate) struct ExpandEnsures;

impl AttrProcMacro for ExpandRequires {
    fn expand<'cx>(
        &self,
        ecx: &'cx mut ExtCtxt<'_>,
        span: Span,
        annotation: TokenStream,
        annotated: TokenStream,
    ) -> Result<TokenStream, ErrorGuaranteed> {
        expand_contract_clause_tts(ecx, span, annotation, annotated, kw::ContractRequires)
    }
}

impl AttrProcMacro for ExpandEnsures {
    fn expand<'cx>(
        &self,
        ecx: &'cx mut ExtCtxt<'_>,
        span: Span,
        annotation: TokenStream,
        annotated: TokenStream,
    ) -> Result<TokenStream, ErrorGuaranteed> {
        expand_contract_clause_tts(ecx, span, annotation, annotated, kw::ContractEnsures)
    }
}

// Trust: expanders for the trust-spec attribute surface (`trust::requires` /
// `trust::ensures`, substituted by the resolver's spec-contract hook). They
// perform the same signature rewrite as the upstream expanders but inject the
// Trust-specific clause keywords, so the parser can tell a Trust-origin clause
// (whose payload may be spec-only syntax like `result`, `old()`, `forall`,
// `==>` that must never be name-resolved or type-checked) from an upstream
// `core::contracts` clause (which keeps upstream's typed lowering unchanged).

pub(crate) struct ExpandTrustRequires;

pub(crate) struct ExpandTrustEnsures;

impl AttrProcMacro for ExpandTrustRequires {
    fn expand<'cx>(
        &self,
        ecx: &'cx mut ExtCtxt<'_>,
        span: Span,
        annotation: TokenStream,
        annotated: TokenStream,
    ) -> Result<TokenStream, ErrorGuaranteed> {
        expand_contract_clause_tts(ecx, span, annotation, annotated, kw::TrustContractRequires)
    }
}

impl AttrProcMacro for ExpandTrustEnsures {
    fn expand<'cx>(
        &self,
        ecx: &'cx mut ExtCtxt<'_>,
        span: Span,
        annotation: TokenStream,
        annotated: TokenStream,
    ) -> Result<TokenStream, ErrorGuaranteed> {
        expand_contract_clause_tts(ecx, span, annotation, annotated, kw::TrustContractEnsures)
    }
}

/// Trust (D4, "one implementation, two surfaces"): the compat desugaring for a
/// first-class clause that has NO second implementation to desugar into.
///
/// `ExpandTrustRequires` / `ExpandTrustEnsures` inject a dedicated Trust clause
/// KEYWORD plus a braced payload, which the parser then routes to its own
/// `TrustContractClause` code path — a second implementation that has already
/// drifted from the native one it is supposed to mirror. This expander instead
/// injects the NATIVE CLAUSE SPELLING VERBATIM: the contextual clause ident
/// followed by the author's own payload tokens, unwrapped. The token stream
/// handed to the parser is then byte-for-byte the stream the author would have
/// produced by writing the first-class clause directly, so
///
/// Trust: the two surfaces live in distinct modules with a complete typed payload.
/// ```rust
/// mod compatibility {
///     #[trust::decreases(e)]
///     pub fn f(e: u32) -> u32 { e }
/// }
/// mod native {
///     pub fn f(e: u32) -> u32 decreases e { e }
/// }
/// ```
///
/// cannot diverge: there is nothing to diverge, only one parse and one lane.
/// That is design-of-record v3's "attribute spellings = compat desugaring only"
/// made literal rather than asserted.
///
/// The payload is deliberately NOT brace-wrapped. Braces would reintroduce a
/// distinguishable attribute-origin form and hand the parser a token shape no
/// author can write, which is exactly how the requires/ensures lanes drifted.
/// An empty payload therefore reaches the native clause parser as a missing
/// predicate and is refused there ("expected a predicate expression after the
/// contract clause keyword") rather than being silently dropped here.
fn expand_trust_native_clause_tts(
    ecx: &mut ExtCtxt<'_>,
    attr_span: Span,
    annotation: TokenStream,
    annotated: TokenStream,
    clause_ident: Symbol,
) -> Result<TokenStream, ErrorGuaranteed> {
    // Def-site context for the injected clause ident only. The payload tokens
    // keep the author's own spans and hygiene: they are verifier vocabulary
    // that the native lane never name-resolves, and their spans are what the
    // clause diagnostics point at.
    let ident_span = ecx.with_def_site_ctxt(attr_span);
    expand_contract_clause(ecx, attr_span, annotated, |new_tts| {
        // Upstream 1.101: the injector writes into a plain `Vec<TokenTree>`
        // (the old `push_tree` builder API is gone).
        new_tts.push(TokenTree::Token(
            token::Token::from_ast_ident(Ident::new(clause_ident, ident_span)),
            Spacing::Alone,
        ));
        for tt in annotation.iter() {
            new_tts.push(tt.clone());
        }
        Ok(())
    })
}

pub(crate) struct ExpandTrustDecreases;

impl AttrProcMacro for ExpandTrustDecreases {
    fn expand<'cx>(
        &self,
        ecx: &'cx mut ExtCtxt<'_>,
        span: Span,
        annotation: TokenStream,
        annotated: TokenStream,
    ) -> Result<TokenStream, ErrorGuaranteed> {
        expand_trust_native_clause_tts(ecx, span, annotation, annotated, sym::decreases)
    }
}

/// Trust: the refusal expander for `#[trust::invariant(..)]`.
///
/// This is deliberately NOT a lowering, and it must never become one.
///
/// WHAT IT REPLACES. `trust-spec` exports an `invariant` passthrough proc
/// macro, and until this expander existed the resolver had no mapping for it,
/// so the proc macro RAN and returned the item unchanged. MEASURED on
/// `trust-e26541e3`: a file carrying `#[trust::invariant(false)]` and the same
/// file with the attribute deleted produce a BIT-IDENTICAL obligation set, and
/// `#[trust::invariant(this is not even an expression ~~~)]` compiles clean with
/// exit 0. The attribute looked like a specification and contributed nothing —
/// a reader, and a ratchet, would both count it as a guarantee.
///
/// WHY REFUSE RATHER THAN LOWER. There is no defined semantics for a
/// function-position `invariant`:
///
/// * The real loop-invariant machinery is keyed to a loop.
///   `rustc_hir::LoopClause::loop_id` is documented as "the authoritative
///   in-crate association key" for the `while` expression the clause belongs
///   to. An attribute on a function has no loop to bind to.
/// * The one existing non-loop target, `trust_types::VcKind::ContractInvariant`,
///   carries only the clause text and no program point: `trust-vcgen` refutes it
///   as a bare `Not(predicate)`. MEASURED via the `register_tool` lane, that
///   makes the obligation PROVED exactly when the predicate is a TAUTOLOGY —
///   `#[trust::invariant(1 == 1)]` reports `outcome=proved` while the same
///   function's real `overflow:add` obligation stays `failed`. Routing this
///   attribute there would not merely fail to help; it would MANUFACTURE a
///   proved row that constrains nothing and inflate the verified count.
///
/// So the fragment is not widened by approximation. The construct is named and
/// refused, and the diagnostic carries the fixes that do have exact semantics.
pub(crate) struct ExpandTrustInvariant;

impl AttrProcMacro for ExpandTrustInvariant {
    fn expand<'cx>(
        &self,
        ecx: &'cx mut ExtCtxt<'_>,
        span: Span,
        _annotation: TokenStream,
        _annotated: TokenStream,
    ) -> Result<TokenStream, ErrorGuaranteed> {
        // Fail closed and fail LOUD. Returning `Err` aborts expansion of this
        // item, so no silently-unverified code can reach codegen.
        Err(ecx
            .sess
            .dcx()
            .struct_span_err(span, "`trust::invariant` is not a verified contract surface")
            .with_note(
                "this attribute used to be accepted and silently discarded: it produced no \
                 obligation and no diagnostic, so it stated a guarantee that was never checked",
            )
            .with_note(
                "an `invariant` must name the program point it constrains; an attribute on an \
                 item has no loop to bind to, so it has no exact meaning to lower",
            )
            .with_help(
                "for a loop invariant, use the first-class loop clause: \
                 `while <cond> invariant <predicate> { ... }` or \
                 `loop invariant <predicate> { ... }`",
            )
            .with_help(
                "for a condition that must hold on entry, use `#[trust::requires(<predicate>)]`",
            )
            .with_help(
                "for a condition that must hold on return, use \
                 `#[trust::ensures(move |r: &T| <predicate>)]`",
            )
            .with_help("otherwise delete the attribute: leaving it in place states nothing")
            .emit_err())
    }
}

/// Expand the function signature to include the first-class contract clause.
///
/// tRustc uses Rust-compatible attribute syntax, but the compiler owns the
/// resulting contract object. Verification must consume the typed contract
/// query, not this token-level compatibility transform.
///
/// The contracts clause will be injected before the function body and the optional where clause.
/// For that, we search for the body / where token, and invoke the `inject` callback to generate the
/// contract clause in the right place.
///
// FIXME: this kind of manual token tree munging does not have significant precedent among
// rustc builtin macros, probably because most builtin macros use direct AST manipulation to
// accomplish similar goals. But since our attributes need to take arbitrary expressions, and
// our attribute infrastructure does not yet support mixing a token-tree annotation with an AST
// annotated, we end up doing token tree manipulation.
fn expand_contract_clause(
    ecx: &mut ExtCtxt<'_>,
    attr_span: Span,
    annotated: TokenStream,
    inject: impl FnOnce(&mut Vec<TokenTree>) -> Result<(), ErrorGuaranteed>,
) -> Result<TokenStream, ErrorGuaranteed> {
    let mut new_tts = vec![];
    let mut cursor = annotated.iter();

    let is_kw = |tt: &TokenTree, sym: Symbol| {
        if let TokenTree::Token(token, _) = tt { token.is_ident_named(sym) } else { false }
    };

    // Find the `fn` keyword to check if this is a function.
    if cursor
        .find(|tt| {
            new_tts.push((*tt).clone());
            is_kw(tt, kw::Fn)
        })
        .is_none()
    {
        return Err(ecx
            .sess
            .dcx()
            .span_err(attr_span, "contract annotations can only be used on functions"));
    }

    // Contracts are not yet supported on async/gen functions
    if new_tts.iter().any(|tt| is_kw(tt, kw::Async) || is_kw(tt, kw::Gen)) {
        return Err(ecx.sess.dcx().span_err(
            attr_span,
            "contract annotations are not yet supported on async or gen functions",
        ));
    }

    // Found the `fn` keyword, now find either the `where` token or the function body.
    let next_tt = loop {
        let Some(tt) = cursor.next() else {
            return Err(ecx.sess.dcx().span_err(
                attr_span,
                "contract annotations is only supported in functions with bodies",
            ));
        };
        // If `tt` is the last element. Check if it is the function body.
        if cursor.peek().is_none() {
            if let TokenTree::Delimited(_, _, token::Delimiter::Brace, _) = tt {
                break tt;
            } else {
                return Err(ecx.sess.dcx().span_err(
                    attr_span,
                    "contract annotations is only supported in functions with bodies",
                ));
            }
        }

        if is_kw(tt, kw::Where) {
            break tt;
        }
        new_tts.push(tt.clone());
    };

    // At this point, we've transcribed everything from the `fn` through the formal parameter list
    // and return type declaration, (if any), but `tt` itself has *not* been transcribed.
    //
    // Now inject the AST contract form.
    //
    inject(&mut new_tts)?;

    // Above we injected the internal AST requires/ensures construct. Now copy over all the other
    // token trees.
    new_tts.push(next_tt.clone());
    while let Some(tt) = cursor.next() {
        new_tts.push(tt.clone());
        if cursor.peek().is_none()
            && !matches!(tt, TokenTree::Delimited(_, _, token::Delimiter::Brace, _))
        {
            return Err(ecx.sess.dcx().span_err(
                attr_span,
                "contract annotations is only supported in functions with bodies",
            ));
        }
    }

    Ok(TokenStream::new(new_tts))
}

fn expand_contract_clause_tts(
    ecx: &mut ExtCtxt<'_>,
    attr_span: Span,
    annotation: TokenStream,
    annotated: TokenStream,
    clause_keyword: rustc_span::Symbol,
) -> Result<TokenStream, ErrorGuaranteed> {
    if annotation.is_empty() {
        let (name, example) = if clause_keyword == kw::ContractRequires {
            ("requires", "condition")
        } else {
            ("ensures", "|result: &T| condition")
        };
        ecx.sess.dcx().span_err(
            attr_span,
            format!("`{name}` attribute requires an argument, e.g., `#[{name}({example})]`"),
        );
        // Returning `Err` would replace it with a dummy fragment and cause cascading name-resolution errors.
        // Instead, we return the original token stream so that there is no later noises.
        return Ok(annotated);
    }

    let feature_span = ecx.with_def_site_ctxt(attr_span);
    expand_contract_clause(ecx, attr_span, annotated, |new_tts| {
        new_tts.push(TokenTree::Token(
            token::Token::from_ast_ident(Ident::new(clause_keyword, feature_span)),
            Spacing::Joint,
        ));
        new_tts.push(TokenTree::Delimited(
            DelimSpan::from_single(attr_span),
            DelimSpacing::new(Spacing::JointHidden, Spacing::JointHidden),
            token::Delimiter::Brace,
            annotation,
        ));
        Ok(())
    })
}
