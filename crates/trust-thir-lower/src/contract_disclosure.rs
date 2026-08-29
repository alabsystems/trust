// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! Contract carry into the direct Module — increment IR-3 of
//! `docs/design/2026-08-27-two-language-direct-to-trust-ir.md` (§5).
//!
//! Principle 5 names the gap this narrows: "source contracts, state epochs,
//! typed formulas, and obligation ownership are not yet bound to Trust-IR SSA
//! values." The claim-bearing binding (`Function.summary` /
//! `proof_obligations`) is BLOCKED by design under `structural-parity-only-v1`
//! — `direct_authority_inventory_errors` fails finalization on any such
//! population, and that tripwire is on the audit's DO-NOT-TOUCH list. This
//! module is the lawful increment: the authored contracts ride the established
//! NON-CLAIM channel — a `DesignOnly` `SpecModule`, the same channel
//! temporal-carry and the deferred-verification disclosure already use.
//!
//! # Honesty contract (design §5, review-amended)
//!
//! * Source of truth is the typed `trust_contracts` query, behind its own
//!   `def_may_have_contracts` pre-filter (the query's disk-cache contract:
//!   only invoked for items that have contracts). Never `span_to_snippet`,
//!   never `syn`.
//! * The channel is string-typed (`SpecInvariant.formula` is an opaque string
//!   by design), so this is a STRING-RENDERED disclosure: the typed
//!   `TrustContractProposition` tree is rendered by exactly ONE
//!   compiler-authoritative renderer (below), deterministic and
//!   schema-tagged (`trust.contract-disclosure.v1`), on the v6/D1 discipline —
//!   the compiler renders, consumers decode the versioned schema, nothing
//!   offline re-elaborates. The typed-slot wire property is reserved for the
//!   `contract-bound-v2` capability tier.
//! * `Opaque`/`Unsupported`/`MirLocal` clauses are carried AS SUCH — disclosed,
//!   never invented, never silently dropped.
//! * The `FuncId` binding is serialized in every row (not only the def-path
//!   text), keyed by the assembled `assigned` map.
//! * Loop contracts stay in their own lane (E4/E5 owns them); this module
//!   reads only the dense function-contract table.

use rustc_middle::mir::trust_contract::{
    TrustContract, TrustContractBundle, TrustContractPredicateKind, TrustContractProposition,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefId, DefIndex, LocalDefId};
use trust_ir::Module;
use trust_ir::{SpecInvariant, SpecModule};
use trust_ir::value::FuncId;

/// The disclosure SpecModule name. Reserved.
pub const CONTRACT_DISCLOSURE_NAME: &str = "@trust-internal::contract-disclosure-v1";

/// Install the contract disclosure for every assembled body that carries
/// authored contracts. Inert (installs nothing) on a contract-free crate, so
/// un-annotated crates get byte-identical artifacts.
///
/// Returns an error only on the reserved-name collision; the caller treats it
/// like its other finalization errors.
pub fn install_contract_disclosure(
    tcx: TyCtxt<'_>,
    assigned: &[(u32, FuncId)],
    module: &mut Module,
) -> Result<(), String> {
    if module.spec_modules.iter().any(|spec| spec.name == CONTRACT_DISCLOSURE_NAME) {
        return Err(format!(
            "reserved contract disclosure name collision: {CONTRACT_DISCLOSURE_NAME}"
        ));
    }

    let mut disclosure = SpecModule::new(CONTRACT_DISCLOSURE_NAME);
    for &(def_index, func_id) in assigned {
        let def_id =
            DefId { krate: rustc_span::def_id::LOCAL_CRATE, index: DefIndex::from_u32(def_index) };
        let Some(local) = def_id.as_local() else { continue };
        if !may_have_contracts(tcx, local) {
            continue;
        }
        let bundle = tcx.trust_contracts(def_id);
        let def_path = tcx.def_path_str(def_id);
        for (i, contract) in bundle.contracts.iter().enumerate() {
            disclosure.invariants.push(SpecInvariant::new(
                format!("fn:{}:{}:{i}", func_id.index(), kind_tag(contract)),
                render_row(func_id, &def_path, contract),
            ));
        }
    }
    if !disclosure.invariants.is_empty() {
        module.spec_modules.push(disclosure);
    }
    Ok(())
}

/// The query's own pre-filter: `trust_contracts` may only be invoked for items
/// that can carry contracts (its disk-cache contract).
fn may_have_contracts(tcx: TyCtxt<'_>, local: LocalDefId) -> bool {
    TrustContractBundle::def_may_have_contracts(tcx, local)
}

fn kind_tag(contract: &TrustContract<'_>) -> &'static str {
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

/// THE compiler-authoritative renderer (design §5): one deterministic JSON
/// rendering of a contract row, schema-tagged. Consumers decode this schema;
/// nothing re-parses authored text.
fn render_row(func_id: FuncId, def_path: &str, contract: &TrustContract<'_>) -> String {
    let predicate = match &contract.predicate.kind {
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
    };
    format!(
        "{{\"schema\":\"trust.contract-disclosure.v1\",\"func_id\":{},\"def_path\":\"{}\",\
         \"kind\":\"{}\",\"non_claim\":\"DesignOnly disclosure: these are the AUTHORED \
         clauses, carried unproven; nothing here is a verdict\",\"predicate\":{predicate}}}",
        func_id.index(),
        esc(def_path),
        kind_tag(contract),
    )
}

/// Deterministic recursive JSON rendering of the closed proposition
/// vocabulary. A new variant is a compile error here — a forced decision about
/// its disclosure spelling.
fn render_proposition(p: &TrustContractProposition) -> String {
    use TrustContractProposition as P;
    match p {
        P::Bool(b) => format!("{{\"bool\":{b}}}"),
        P::Int(i) => format!("{{\"int\":\"{i}\"}}"),
        P::UInt(u) => format!("{{\"uint\":\"{u}\"}}"),
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

fn esc(s: &str) -> String {
    crate::clean_origin_join::json_escape_min(s)
}
