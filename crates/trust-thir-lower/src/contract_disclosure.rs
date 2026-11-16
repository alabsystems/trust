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
//!   compiler-authoritative renderer (`crate::contract_render`, moved there
//!   unchanged by WS5.5 step 1), deterministic and schema-tagged
//!   (`trust.contract-disclosure.v1`), on the v6/D1 discipline — the compiler
//!   renders, consumers decode the versioned schema, nothing offline
//!   re-elaborates. The typed-slot wire property is reserved for the
//!   contract-bound capability tier: design name `contract-bound-v2` (08-27
//!   §5) = coverage marker `contract-bound-v3` (shipped markers carry the rung
//!   ORDINAL; ordinal 2 is `obligation-bearing-pending-v2`, and under D36/D37
//!   the Clean carrier is a codegen-license authority, not a rung). It is
//!   built STAGED in `crate::contract_carry` (WS5.5); the owner-signed flip
//!   (DG-60) that installs it deletes this module's install call, so zero
//!   `DesignOnly` contract rows remain (G6). The disclosure NAME stays
//!   reserved so an old artifact is never reinterpreted.
//! * `Opaque`/`Unsupported`/`MirLocal` clauses are carried AS SUCH — disclosed,
//!   never invented, never silently dropped.
//! * The `FuncId` binding is serialized in every row (not only the def-path
//!   text), keyed by the assembled `assigned` map.
//! * Loop contracts stay in their own lane (E4/E5 owns them); this module
//!   reads only the dense function-contract table.

use rustc_middle::mir::trust_contract::{TrustContract, TrustContractBundle};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefId, DefIndex, LocalDefId};
use trust_ir::value::FuncId;
use trust_ir::{Module, SpecInvariant, SpecModule};

// WS5.5 step 1: the renderer moved, unchanged, to `crate::contract_render` so
// the staged contract carry (`crate::contract_carry`) renders the SAME bytes.
use crate::contract_render::{esc, kind_tag, render_predicate};

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
        // `with_no_trimmed_paths!` for two independent reasons — the first is the
        // one `crate_module::record` and `instance_flip.rs` document for their own
        // `def_path_str`:
        //
        // 1. TERMINATION. A bare `def_path_str` runs the `trimmed_def_paths`
        //    query, which arms rustc's `must_produce_diag`; `DiagCtxtInner::drop`
        //    then ICEs if the compilation emits no diagnostic. This row is
        //    artifact text, not a diagnostic, and it runs for EVERY
        //    contract-bearing body. Under `-Ztrust-verify-output=json` with a
        //    human `--error-format` (the raw-trustc wire) a fully proved,
        //    island-free crate prints no diagnostic at all, so every such crate
        //    exited 101 AFTER its proved rows were written
        //    (`tests/ui/trust/json_output_contract_only_no_ice.rs`). Text mode
        //    and island crates escaped only because a verification/kernel
        //    `note:` happened to satisfy the assertion.
        // 2. DETERMINISM. A trimmed path is the shortest spelling that is
        //    unambiguous IN THIS COMPILATION'S import context — `keep` today,
        //    `m::keep` once a dependency exports another `keep`. The module
        //    header promises "one deterministic rendering"; a disclosure row
        //    whose `def_path` varies with unrelated crates is not one. It is also
        //    the spelling the coverage rows carry, so the disclosure row and the
        //    coverage row stay directly comparable.
        let def_path = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def_id));
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

/// THE compiler-authoritative renderer (design §5): one deterministic JSON
/// rendering of a contract row, schema-tagged. Consumers decode this schema;
/// nothing re-parses authored text.
fn render_row(func_id: FuncId, def_path: &str, contract: &TrustContract<'_>) -> String {
    let predicate = render_predicate(&contract.predicate.kind);
    format!(
        "{{\"schema\":\"trust.contract-disclosure.v1\",\"func_id\":{},\"def_path\":\"{}\",\
         \"kind\":\"{}\",\"non_claim\":\"DesignOnly disclosure: these are the AUTHORED \
         clauses, carried unproven; nothing here is a verdict\",\"predicate\":{predicate}}}",
        func_id.index(),
        esc(def_path),
        kind_tag(contract),
    )
}

#[cfg(test)]
mod tests;
