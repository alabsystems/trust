// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//
//! Compatibility macros for source-embedded temporal models.
//!
//! `trust_model!` expands the legacy near-plain-Rust DSL to a
//! `::trust_spec_temporal::Model` literal. Its capability — a bounded
//! scalar-integer SAFETY machine — is `FullyReplaced` by the live Clean lane
//! (owner policy flip 2026-07-21): author a temporal `Model` (or a
//! `clean { … }` island) and certify it with
//! `certify_clean_scalar_model_with_ty`. The formerly narrower Clean admission
//! domain now covers the owner-ratified operational macro-parity domain — the
//! process-global interner and its name caps were deleted, the
//! expression-depth cap was widened to a 65_536-level decode-cost guard, and
//! positive near-cap vectors certify end-to-end — so per the scorecard-derived
//! policy `trust_model!` carries the advisory `#[deprecated]` nudge (the D1+
//! ratchet). Adding the deprecation attribute does not further change the
//! current constructor expansion: existing constructor uses keep compiling and
//! behaving identically; the nudge is advisory migration guidance, not a
//! removal. This does not restore the separately retired, non-evidentiary
//! link-time inventory described below.
//!
//! `temporal_model!` (the item-position sibling) carries the same advisory
//! nudge: it exercises the same `FullyReplaced` scalar-safety core. Its former
//! extra capability — automatic link-time model inventory — was deleted as
//! extraneous (owner ruling 2026-07-20, "no deprecation limbo"): the live
//! Targo gates never trusted the linked registry, so the macro now expands to
//! the model constructor only and callers enumerate the definitions they
//! certify explicitly. See `trust_spec_temporal::r5_scorecard` for the
//! machine-checkable capability scorecard that derives, per macro, whether the
//! nudge fires; its source cross-check requires the attribute below to stay in
//! lockstep with the scorecard. Macro DELETION remains separately gated
//! (retirement blockers).
//!
//! Neither macro is removed, and deprecation does not change either current
//! constructor expansion: existing constructor uses keep working identically.
//! The earlier removal of `temporal_model!`'s untrusted inventory arm remains
//! intentional. `targo trust temporal` only inspects the
//! dependency/linkable-target boundary and deliberately exits fail-closed; it
//! does not execute or authenticate a project proof harness.
//!
//! Ported 1:1 from aterm's proven `ty_model!` (`aterm-spec-macros`), renamed and
//! re-pathed to `::trust_spec_temporal::*`. See `docs/TY_ANNOTATION_FEATURE.md`.
//!
//! ```ignore
//! use trust_spec_temporal::{trust_model, Model};
//! fn ring() -> Model {
//!     trust_model! {
//!         Ring {
//!             const MaxSeq = 6;
//!             const Cap = 3;
//!             var seq = 0;
//!             var lo = 1;
//!             action Push when (seq <= MaxSeq - 1) {
//!                 seq = seq + 1;
//!                 lo = if (seq + 1) - lo + 1 > Cap { lo + 1 } else { lo };
//!             }
//!             invariant LenBounded: seq - lo + 1 <= Cap;
//!         }
//!     }
//! }
//! ```
//!
//! Identifiers declared `const` become TLA+ `CONSTANT`s; declared `var`s are state
//! variables. An action may be unguarded or use `when (GUARD)`. The complete
//! expression grammar is integer literals, simple identifier paths, parentheses,
//! `+`, `-`, `>`, `<=`, `==`, and nested `if/else` (mapped to the `Expr` builders
//! in `trust_spec_temporal`). By convention a model declares
//! `const Buggy = 0`. The linked-library certification API requires a bound,
//! kernel-rechecked positive certificate and a replay-verified counterexample
//! at `Buggy = 1` (non-vacuity); macro expansion alone grants no proof credit.

use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

/// Expand a `trust_model! { Name { .. } }` annotation to a
/// `::trust_spec_temporal::Model` literal.
///
/// D1+ ratchet (owner policy flip 2026-07-21): every capability this macro
/// exercises is `FullyReplaced` by the live Clean lane
/// (`trust_spec_temporal::r5_scorecard`) — the admission-domain and interner
/// gaps are closed with positive near-cap certified vectors — so per the
/// scorecard-derived policy the macro carries the advisory `#[deprecated]`
/// nudge, satisfying the PRIME RULE (the replacement reproduces the macro's
/// verdict for every model in the ratified parity domain). Expansion is
/// unchanged and every existing use still works identically; only macro
/// DELETION remains separately gated (retirement blockers).
#[proc_macro]
#[deprecated(note = "author a temporal Model (or a `clean { … }` island) and certify with \
            `certify_clean_scalar_model_with_ty` — the Clean scalar lane is the closed, \
            byte-identical replacement (R5 scorecard, owner policy flip 2026-07-21)")]
pub fn trust_model(input: TokenStream) -> TokenStream {
    let def = parse_macro_input!(input as ModelDef);
    match def.expand() {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Item-position form of [`trust_model!`].
///
/// `temporal_model! { Name { .. } }` at item scope expands to
/// `pub fn <snake_name>_model() -> ::trust_spec_temporal::Model { <literal> }`.
///
/// The macro's former second expansion — an `inventory::submit!` into a
/// link-time model registry — was deleted as extraneous (owner ruling
/// 2026-07-20): the live Targo temporal/build gates never trusted that
/// process-owned registry as program evidence and unconditionally reject the
/// automatic route with unbound-evidence exit 2. Model discovery is explicit:
/// the caller or build integration invokes
/// `certify_clean_scalar_model_with_ty` (or the explicit `check_models_*`
/// APIs) for the exact definitions it owns.
///
/// D1+ ratchet (owner policy flip 2026-07-21): `temporal_model!` carries the
/// same advisory `#[deprecated]` nudge as [`trust_model!`] — it exercises the
/// same `FullyReplaced` scalar-safety core, so the scorecard-derived policy
/// requires the attribute. Its current constructor form keeps working
/// identically; the separately retired, non-evidentiary inventory arm remains
/// unavailable. Only macro DELETION is gated (retirement blockers).
#[proc_macro]
#[deprecated(note = "author a temporal Model (or a `clean { … }` island) and certify with \
            `certify_clean_scalar_model_with_ty` — the Clean scalar lane is the closed, \
            byte-identical replacement (R5 scorecard, owner policy flip 2026-07-21)")]
pub fn temporal_model(input: TokenStream) -> TokenStream {
    let def = parse_macro_input!(input as ModelDef);
    let model_lit = match def.expand() {
        Ok(ts) => ts,
        Err(e) => return e.to_compile_error().into(),
    };
    let name_str = def.name.to_string();
    // Constructor fn name: snake_case(Name) + "_model" (matches the proven
    // aterm convention, e.g. Ring -> ring_model).
    let fn_ident = syn::Ident::new(&format!("{}_model", to_snake_case(&name_str)), def.name.span());
    quote! {
        pub fn #fn_ident() -> ::trust_spec_temporal::Model { #model_lit }
    }
    .into()
}

/// Convert an UpperCamel / mixed identifier to snake_case (ASCII).
fn to_snake_case(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    for (i, c) in s.chars().enumerate() {
        if c.is_ascii_uppercase() {
            if i != 0 {
                out.push('_');
            }
            out.push(c.to_ascii_lowercase());
        } else {
            out.push(c);
        }
    }
    out
}

struct ActionDef {
    name: syn::Ident,
    guard: Option<syn::Expr>,
    updates: Vec<(syn::Ident, syn::Expr)>,
}

struct ModelDef {
    name: syn::Ident,
    consts: Vec<(syn::Ident, i64)>,
    vars: Vec<(syn::Ident, i64)>,
    actions: Vec<ActionDef>,
    invariants: Vec<(syn::Ident, syn::Expr)>,
}

impl syn::parse::Parse for ModelDef {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let name: syn::Ident = input.parse()?;
        let body;
        syn::braced!(body in input);
        let mut consts = Vec::new();
        let mut vars = Vec::new();
        let mut actions = Vec::new();
        let mut invariants = Vec::new();
        while !body.is_empty() {
            if body.peek(syn::Token![const]) {
                body.parse::<syn::Token![const]>()?;
                let id: syn::Ident = body.parse()?;
                body.parse::<syn::Token![=]>()?;
                let lit: syn::LitInt = body.parse()?;
                body.parse::<syn::Token![;]>()?;
                consts.push((id, lit.base10_parse::<i64>()?));
                continue;
            }
            let kw: syn::Ident = body.parse()?;
            match kw.to_string().as_str() {
                "var" => {
                    let id: syn::Ident = body.parse()?;
                    body.parse::<syn::Token![=]>()?;
                    let lit: syn::LitInt = body.parse()?;
                    body.parse::<syn::Token![;]>()?;
                    vars.push((id, lit.base10_parse::<i64>()?));
                }
                "action" => {
                    let aname: syn::Ident = body.parse()?;
                    let guard = if body.peek(syn::Ident) {
                        let w: syn::Ident = body.parse()?;
                        if w != "when" {
                            return Err(syn::Error::new(w.span(), "expected `when` or `{`"));
                        }
                        let g;
                        syn::parenthesized!(g in body);
                        Some(g.parse::<syn::Expr>()?)
                    } else {
                        None
                    };
                    let ab;
                    syn::braced!(ab in body);
                    let mut updates = Vec::new();
                    while !ab.is_empty() {
                        let lhs: syn::Ident = ab.parse()?;
                        ab.parse::<syn::Token![=]>()?;
                        let rhs: syn::Expr = ab.parse()?;
                        ab.parse::<syn::Token![;]>()?;
                        updates.push((lhs, rhs));
                    }
                    actions.push(ActionDef { name: aname, guard, updates });
                }
                "invariant" => {
                    let iname: syn::Ident = body.parse()?;
                    body.parse::<syn::Token![:]>()?;
                    let e: syn::Expr = body.parse()?;
                    body.parse::<syn::Token![;]>()?;
                    invariants.push((iname, e));
                }
                other => {
                    return Err(syn::Error::new(
                        kw.span(),
                        format!("expected const/var/action/invariant, found `{other}`"),
                    ));
                }
            }
        }
        Ok(ModelDef { name, consts, vars, actions, invariants })
    }
}

impl ModelDef {
    fn expand(&self) -> syn::Result<proc_macro2::TokenStream> {
        let const_names: std::collections::HashSet<String> =
            self.consts.iter().map(|(id, _)| id.to_string()).collect();
        let name_str = self.name.to_string();

        let consts_toks = self.consts.iter().map(|(id, v)| {
            let s = id.to_string();
            quote! { (#s, #v) }
        });
        let vars_toks = self.vars.iter().map(|(id, v)| {
            let s = id.to_string();
            quote! { ::trust_spec_temporal::StateVar { name: #s, init: #v } }
        });

        let mut actions_toks = Vec::new();
        for a in &self.actions {
            let an = a.name.to_string();
            let guard = match &a.guard {
                Some(g) => {
                    let t = tr_expr(g, &const_names)?;
                    quote! { Some(#t) }
                }
                None => quote! { None },
            };
            let mut ups = Vec::new();
            for (lhs, rhs) in &a.updates {
                let s = lhs.to_string();
                let t = tr_expr(rhs, &const_names)?;
                ups.push(quote! { ::trust_spec_temporal::Update { var: #s, expr: #t } });
            }
            actions_toks.push(quote! {
                ::trust_spec_temporal::Action { name: #an, guard: #guard, updates: vec![ #(#ups),* ] }
            });
        }

        let mut invs_toks = Vec::new();
        for (id, e) in &self.invariants {
            let s = id.to_string();
            let t = tr_expr(e, &const_names)?;
            invs_toks.push(quote! { ::trust_spec_temporal::Invariant { name: #s, expr: #t } });
        }

        Ok(quote! {
            ::trust_spec_temporal::Model {
                name: #name_str,
                consts: vec![ #(#consts_toks),* ],
                vars: vec![ #(#vars_toks),* ],
                fn_vars: vec![],
                actions: vec![ #(#actions_toks),* ],
                invariants: vec![ #(#invs_toks),* ],
            }
        })
    }
}

/// The single tail expression of a one-expression block (`{ expr }`).
fn block_tail(block: &syn::Block) -> syn::Result<&syn::Expr> {
    if let [syn::Stmt::Expr(e, None)] = block.stmts.as_slice() {
        Ok(e)
    } else {
        Err(syn::Error::new_spanned(block, "if/else branch must be a single expression"))
    }
}

/// Translate the else branch (a `{ block }` or a nested `if`) to an `Expr`.
fn tr_else(
    e: &syn::Expr,
    consts: &std::collections::HashSet<String>,
) -> syn::Result<proc_macro2::TokenStream> {
    match e {
        syn::Expr::Block(b) => tr_expr(block_tail(&b.block)?, consts),
        _ => tr_expr(e, consts),
    }
}

/// Translate a restricted `syn::Expr` to `trust_spec_temporal::Expr` builder calls.
fn tr_expr(
    e: &syn::Expr,
    consts: &std::collections::HashSet<String>,
) -> syn::Result<proc_macro2::TokenStream> {
    match e {
        syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(i), .. }) => {
            let v: i64 = i.base10_parse()?;
            Ok(quote! { ::trust_spec_temporal::int(#v) })
        }
        syn::Expr::Path(p) => {
            if let Some(id) = p.path.get_ident() {
                let id = id.to_string();
                if consts.contains(&id) {
                    Ok(quote! { ::trust_spec_temporal::cst(#id) })
                } else {
                    Ok(quote! { ::trust_spec_temporal::var(#id) })
                }
            } else {
                Err(syn::Error::new_spanned(e, "expected a simple identifier"))
            }
        }
        syn::Expr::Paren(p) => tr_expr(&p.expr, consts),
        syn::Expr::Binary(b) => {
            let l = tr_expr(&b.left, consts)?;
            let r = tr_expr(&b.right, consts)?;
            let f = match b.op {
                syn::BinOp::Add(_) => quote! { ::trust_spec_temporal::add },
                syn::BinOp::Sub(_) => quote! { ::trust_spec_temporal::sub },
                syn::BinOp::Gt(_) => quote! { ::trust_spec_temporal::gt },
                syn::BinOp::Le(_) => quote! { ::trust_spec_temporal::le },
                syn::BinOp::Eq(_) => quote! { ::trust_spec_temporal::eq },
                _ => {
                    return Err(syn::Error::new_spanned(
                        e,
                        "unsupported operator (use + - > <= ==)",
                    ));
                }
            };
            Ok(quote! { #f(#l, #r) })
        }
        syn::Expr::If(ifx) => {
            let Some((_, else_expr)) = &ifx.else_branch else {
                return Err(syn::Error::new_spanned(e, "`if` must have an `else` branch"));
            };
            let c = tr_expr(&ifx.cond, consts)?;
            let t = tr_expr(block_tail(&ifx.then_branch)?, consts)?;
            let f = tr_else(else_expr, consts)?;
            Ok(quote! { ::trust_spec_temporal::if_(#c, #t, #f) })
        }
        other => Err(syn::Error::new_spanned(other, "unsupported expression in trust_model!")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = "Ring { \
        const MaxSeq = 6; \
        const Buggy = 0; \
        var seq = 0; \
        var lo = 1; \
        action Push when (seq <= MaxSeq) { seq = seq + 1; lo = if seq > 0 { lo + 1 } else { lo }; } \
        invariant Bounded: seq - lo <= 3; \
    }";

    #[test]
    fn snake_case_matches_the_aterm_constructor_convention() {
        assert_eq!(to_snake_case("Ring"), "ring");
        assert_eq!(to_snake_case("EdgeGate"), "edge_gate");
        assert_eq!(to_snake_case("HTTPCache"), "h_t_t_p_cache");
        assert_eq!(to_snake_case("already_snake"), "already_snake");
    }

    #[test]
    fn parser_reads_every_grammar_section() {
        let def: ModelDef = syn::parse_str(SAMPLE).expect("sample model parses");
        assert_eq!(def.name.to_string(), "Ring");
        assert_eq!(def.consts.len(), 2);
        assert_eq!(def.vars.len(), 2);
        assert_eq!(def.actions.len(), 1);
        assert_eq!(def.invariants.len(), 1);
        assert!(def.actions[0].guard.is_some(), "the `when(..)` guard is retained");
        assert_eq!(def.actions[0].updates.len(), 2);
    }

    // D0 capability-preservation guard: the expansion is byte-stable and still
    // hard-codes `fn_vars: vec![]`. A regression that let the macro grow a new
    // capability (e.g. function-valued vars) — one whose replacement is NOT yet
    // live — would change this shape and trip the guard, forcing the scorecard
    // and the deprecation policy to be revisited before shipping.
    #[test]
    fn expansion_is_unchanged_and_stays_scalar_only() {
        let def: ModelDef = syn::parse_str(SAMPLE).expect("sample model parses");
        let expanded = def.expand().expect("sample model expands").to_string();
        assert!(expanded.contains(":: trust_spec_temporal :: Model"), "{expanded}");
        assert!(expanded.contains("fn_vars : vec ! []"), "macro stays scalar-only: {expanded}");
        assert!(expanded.contains(":: trust_spec_temporal :: StateVar"), "{expanded}");
        assert!(expanded.contains(":: trust_spec_temporal :: Action"), "{expanded}");
        assert!(expanded.contains(":: trust_spec_temporal :: Invariant"), "{expanded}");
        // The guarded action keeps its guard as `Some(..)`, never dropped.
        assert!(expanded.contains("Some ("), "guard is preserved in expansion: {expanded}");
    }
}
