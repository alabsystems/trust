// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! THE compiler-authoritative renderer of a typed contract clause — design
//! `docs/design/2026-08-27-two-language-direct-to-trust-ir.md` §5, roadmap
//! WS5.5 step 1.
//!
//! One deterministic, closed-vocabulary JSON rendering of the typed
//! `TrustContractProposition` tree (and of the predicate kinds around it),
//! on the v6/D1 discipline: the compiler renders, consumers decode the
//! versioned schema, nothing offline re-elaborates authored text.
//!
//! MOVED, UNCHANGED, out of `contract_disclosure.rs` (WS5.5 step 1). It has
//! two consumers and the bytes they produce must be the same bytes:
//!
//! * the `DesignOnly` disclosure (`crate::contract_disclosure`, schema
//!   `trust.contract-disclosure.v1`), whose rows stay byte-identical across
//!   the move (pinned by `contract_disclosure::tests::
//!   disclosure_row_bytes_are_pinned_across_the_renderer_move`, whose
//!   expected rows are spelled from the pre-move format strings);
//! * the staged contract carry (`crate::contract_carry`), whose
//!   `trust.contract-clause@1` payload IS [`render_proposition`]'s output.
//!
//! A new proposition or predicate variant is a compile error here — a forced
//! decision about its spelling, made once for both consumers.

use rustc_middle::mir::trust_contract::{
    TrustContract, TrustContractPredicateKind, TrustContractProposition,
};

/// The clause-kind tag both consumers spell (`requires`, `ensures`, …).
pub(crate) fn kind_tag(contract: &TrustContract<'_>) -> &'static str {
    use rustc_middle::mir::trust_contract::TrustContractKind as K;
    match contract.kind {
        K::Requires => "requires",
        K::Ensures => "ensures",
        K::Invariant => "invariant",
        K::LoopInvariant => "loop-invariant",
        K::Decreases => "decreases",
        K::Assumes => "assumes",
        K::Asserts => "asserts",
        K::Refinement => "refinement",
        K::Temporal => "temporal",
    }
}

/// The predicate half of a disclosure row: `{"typed":…}`, `{"opaque":…}`,
/// `{"mir_local":…}`, `{"bool":…}` or `{"unsupported":…}`. Every kind is
/// carried AS SUCH — the authored text where the query kept one, the reason or
/// local where it did not — never invented, never dropped.
pub(crate) fn render_predicate(kind: &TrustContractPredicateKind) -> String {
    match kind {
        TrustContractPredicateKind::Typed { text, proposition } => format!(
            "{{\"typed\":{{\"text\":\"{}\",\"proposition\":{}}}}}",
            esc(text.as_str()),
            render_proposition(proposition),
        ),
        TrustContractPredicateKind::Opaque { text } => {
            format!("{{\"opaque\":{{\"text\":\"{}\"}}}}", esc(text.as_str()))
        }
        TrustContractPredicateKind::MirLocal { local } => {
            format!("{{\"mir_local\":{{\"local\":{}}}}}", local.as_u32())
        }
        TrustContractPredicateKind::BoolLiteral { value } => {
            format!("{{\"bool\":{value}}}")
        }
        TrustContractPredicateKind::Unsupported { reason } => {
            format!("{{\"unsupported\":{{\"reason\":\"{}\"}}}}", esc(reason.as_str()))
        }
    }
}

/// Deterministic recursive JSON rendering of the closed proposition
/// vocabulary. A new variant is a compile error here — a forced decision about
/// its disclosure spelling.
pub(crate) fn render_proposition(p: &TrustContractProposition) -> String {
    use TrustContractProposition as P;
    match p {
        P::Bool(b) => format!("{{\"bool\":{b}}}"),
        P::Int(i) => format!("{{\"int\":\"{i}\"}}"),
        P::UInt(u) => format!("{{\"uint\":\"{u}\"}}"),
        // Bits, not a rendered decimal: the disclosure has to distinguish the two
        // zeroes and preserve a NaN payload, and a shortest-round-trip decimal
        // does neither.
        P::Float { bits, width } => {
            format!("{{\"float\":{{\"bits\":\"{bits}\",\"width\":{width}}}}}")
        }
        P::Var { name, domain } => {
            format!("{{\"var\":{{\"name\":\"{}\",\"domain\":\"{domain:?}\"}}}}", esc(name.as_str()))
        }
        P::Not(a) => format!("{{\"not\":{}}}", render_proposition(a)),
        P::And(xs) => format!("{{\"and\":[{}]}}", render_list(xs)),
        P::Or(xs) => format!("{{\"or\":[{}]}}", render_list(xs)),
        P::Implies(a, b) => render_binary("implies", a, b),
        P::Eq(a, b) => render_binary("eq", a, b),
        P::Lt(a, b) => render_binary("lt", a, b),
        P::Le(a, b) => render_binary("le", a, b),
        P::Gt(a, b) => render_binary("gt", a, b),
        P::Ge(a, b) => render_binary("ge", a, b),
        P::Add(a, b) => render_binary("add", a, b),
        P::Sub(a, b) => render_binary("sub", a, b),
        P::Mul(a, b) => render_binary("mul", a, b),
        P::Div(a, b) => render_binary("div", a, b),
        P::Rem(a, b) => render_binary("rem", a, b),
        P::Neg(a) => format!("{{\"neg\":{}}}", render_proposition(a)),
    }
}

fn render_binary(tag: &str, a: &TrustContractProposition, b: &TrustContractProposition) -> String {
    format!("{{\"{tag}\":[{},{}]}}", render_proposition(a), render_proposition(b))
}

fn render_list(xs: &[TrustContractProposition]) -> String {
    xs.iter().map(render_proposition).collect::<Vec<_>>().join(",")
}

pub(crate) fn esc(s: &str) -> String {
    crate::clean_origin_join::json_escape_min(s)
}
