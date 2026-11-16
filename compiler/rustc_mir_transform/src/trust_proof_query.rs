//! Trust: Query providers for trust_proof_results and trust_proof_telemetry.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0
//!
//! Gated: returns None immediately when `-Z trust-verify=off` disables verification.
//! Follows the coverage_ids_info provider pattern in coverage/query.rs.

use rustc_middle::mir::trust_proof::{TrustProofResults, TrustProofTelemetry};
use rustc_middle::ty::{self, TyCtxt};

use crate::trust_verify;

/// Trust: Query provider for `trust_proof_results`.
///
/// Returns per-function verification results (semantic, deterministic, HashStable).
/// The `arena_cache` modifier handles allocation: we return `Option<TrustProofResults>`
/// (owned) and the query system arenas it to `Option<&'tcx TrustProofResults>`.
pub(crate) fn trust_proof_results<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance_def: ty::InstanceKind<'tcx>,
) -> Option<TrustProofResults> {
    if !trust_verify::verification_enabled(tcx.sess) {
        return None;
    }
    if !instance_has_mir(tcx, instance_def) {
        return None;
    }

    let mir_body = tcx.instance_mir(instance_def);
    trust_verify::collect_proof_results_cached(tcx, mir_body)
}

/// Trust (2026-10-15): does `instance_def` have a MIR body to verify? An `Item` whose
/// `DefId` has none — a foreign `extern` declaration handed to generic code as a value
/// (`it.map(trust_probe_boom)` over `extern "C" { fn trust_probe_boom(..) }`), reached
/// by a caller's premise query (`trait_panic_free::instance_discharges_panic_freedom_
/// modulo`) — has no proof results: `instance_mir` would ask `optimized_mir` of it and
/// the compiler ICEd in `typeck` ("can't type-check body of ..::{extern#0}::..",
/// measured on the stage 1 of the 2026-10-14 merge,
/// `tests/ui/trust/local_item_naming_no_verified_body_as_value.rs#extern_decl_map`).
/// `None` is the answer every caller already reads as "no proof results, never
/// credited" (fail-closed). Shims build their MIR from nothing and are unaffected.
fn instance_has_mir<'tcx>(tcx: TyCtxt<'tcx>, instance_def: ty::InstanceKind<'tcx>) -> bool {
    match instance_def {
        ty::InstanceKind::Item(def_id) => tcx.is_mir_available(def_id),
        _ => true,
    }
}

/// Trust: Query provider for `trust_proof_telemetry`.
///
/// Returns per-function verification telemetry (non-deterministic, NOT HashStable).
/// Contains solver timings and counterexamples for reporting.
/// Uses `no_hash` modifier so timings don't affect incremental compilation.
pub(crate) fn trust_proof_telemetry<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance_def: ty::InstanceKind<'tcx>,
) -> Option<TrustProofTelemetry> {
    if !trust_verify::verification_enabled(tcx.sess) {
        return None;
    }
    // Trust (2026-10-15): the same body-less `Item` guard as `trust_proof_results`.
    if !instance_has_mir(tcx, instance_def) {
        return None;
    }

    let mir_body = tcx.instance_mir(instance_def);
    trust_verify::collect_proof_telemetry_cached(tcx, mir_body)
}
