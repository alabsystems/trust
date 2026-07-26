//! The witness key.
//!
//! v1 ships the SOUND default key (PLAN.md §5): schema version + the root's
//! own body hash + the FULL crate SVH + all upstream SVHs. A hit therefore
//! means byte-identical crate + environment, so by determinism the witness
//! equals what cold typeck would produce for that root — and any intra- or
//! cross-crate impl / `use` / coherence change bumps an SVH and forces a miss,
//! which structurally forecloses the method-resolution / negative-information
//! holes the design's adversarial review identified.
//!
//! The *precise* per-referenced-def key (edit-loop hits without the whole-SVH
//! gate) is UNSOUND until the A1-A3 forest-replay work lands and is not
//! implemented here — see PLAN.md §5, "Two key regimes".

use std::hash::Hasher;

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::stable_hash::StableHasher;
use rustc_hir::def_id::{LOCAL_CRATE, LocalDefId};
use rustc_middle::ty::{TyCtxt, TypeckResults};

/// The sound whole-environment key for a root. Returns `None` if the root has
/// no owner body hash (not a mintable body).
pub fn witness_key<'tcx>(tcx: TyCtxt<'tcx>, root: LocalDefId) -> Option<String> {
    // NB: main renamed OwnerNodes.opt_hash_including_bodies -> opt_hash. It is
    // `Some` only when `needs_hir_hash()` (debug-assertions | incremental |
    // needs-metadata | instrument-coverage | metrics-dir); a pure bin crate with
    // no metadata yields `None` here -> no mint/replay (a coverage limit, not a
    // soundness hole).
    let owner_hash = tcx.opt_hir_owner_nodes(root).and_then(|n| n.opt_hash)?;
    let root_dph = tcx.def_path_hash(root.to_def_id());

    // Environment + full-SVH digest (the soundness backstop). StableHasher is
    // deterministic across processes without a hashing context when fed raw
    // bytes, which is all we need to match a mint run against a warm run.
    let mut h = StableHasher::new();
    h.write(crate::schema::SCHEMA_VERSION.as_bytes());
    h.write_u128(tcx.crate_hash(LOCAL_CRATE).as_u128());
    for cnum in tcx.crates(()) {
        h.write_u128(tcx.crate_hash(*cnum).as_u128());
    }
    let env: Fingerprint = h.finish();
    let (e0, e1) = env.split();

    Some(format!(
        "{}_{}_{:016x}{:016x}",
        root_dph.0.to_hex(),
        owner_hash.to_hex(),
        e0.as_u64(),
        e1.as_u64()
    ))
}

/// The PRECISE per-referenced-def key (PLAN.md §5, Regime 2): schema + the root's
/// own body hash + the identities of every DEFINITION the body's picks resolve to
/// — NO whole-crate SVH. It therefore HITS in the edit loop (an edit to an
/// UNRELATED body leaves this root's own hash + its referenced picks unchanged),
/// unlike `witness_key` which requires the whole crate byte-identical.
///
/// It is UNSOUND ON ITS OWN — the negative-information hole (a newly-added impl /
/// inherent method / glob-import can change an unedited body's pick without
/// touching any referenced identity, and a callee-signature edit keeps the same
/// def_path_hash). It is used ONLY behind the DIFFERENTIAL PARITY GATE
/// (`-Ztrust-witness-precise`): a hit is byte-diffed against real typeck and NEVER
/// trusted directly (the measurement mode returns real typeck's result regardless),
/// so a divergence is observed, not miscompiled. This is the design's shadow-mint
/// surface that must go green over a corpus before the key could ever be trusted
/// (which additionally needs the A1–A3 negative-context recorder + derivation forest).
///
/// Takes the root's `TypeckResults` explicitly (NEVER calls `tcx.typeck(root)`) —
/// it is computed during/after typeck(root) (mint has the cached results; the
/// parity check has `real`), so a self-query would cycle.
pub fn precise_witness_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: LocalDefId,
    tr: &TypeckResults<'tcx>,
) -> Option<String> {
    let owner_hash = tcx.opt_hir_owner_nodes(root).and_then(|n| n.opt_hash)?;
    let root_dph = tcx.def_path_hash(root.to_def_id());

    let mut h = StableHasher::new();
    h.write(crate::schema::SCHEMA_VERSION.as_bytes());
    h.write(b"precise-v1");
    // The identity of every method/operator pick the body resolves, in the body's
    // own stable order. A pick's def_path_hash changing (or a pick appearing/
    // disappearing) bumps the key; everything else — negative information,
    // callee-signature drift — is caught by the parity gate, not the key.
    for (_, res) in tr.type_dependent_defs().items_in_stable_order() {
        match res {
            Ok((_, did)) => h.write(&tcx.def_path_hash(*did).0.to_le_bytes()),
            Err(_) => return None,
        }
    }
    let d: Fingerprint = h.finish();
    let (e0, e1) = d.split();
    Some(format!(
        "{}_{}_{:016x}{:016x}",
        root_dph.0.to_hex(),
        owner_hash.to_hex(),
        e0.as_u64(),
        e1.as_u64()
    ))
}

/// Method/operator-pick admission (the enabled-set widening) is sound ONLY
/// under the whole-environment SVH key: `crate_hash(LOCAL_CRATE)` folds every
/// owner's full HIR (impls / `use` / traits-in-scope) + all upstream crate
/// `Svh`s + `dep_tracking_hash` (incl. edition), and `witness_key` folds
/// `crate_hash(LOCAL)` + every upstream `crate_hash` — so any pick-affecting
/// edit bumps the key (miss, fail-safe). The pick's impl-selection half is
/// additionally re-derived by the checker (`Instance::try_resolve`); only the
/// name/probe-uniqueness half is key-attested (same trust class as rustc's own
/// incremental cache).
///
/// If a precise / per-referenced-def key regime is ever introduced, this MUST
/// become `false` (or method picks re-gated behind A1–A3 forest replay), so
/// method-pick admission fails CLOSED rather than relying on Regime-2 merely
/// being unimplemented. `mintable()`'s method branch and the decode method-pick
/// reconstruction are both gated on it.
pub const METHOD_PICKS_SOUND_UNDER_CURRENT_KEY: bool = true;

/// The crate-store filename stem: the local `StableCrateId`.
pub fn store_stem<'tcx>(tcx: TyCtxt<'tcx>) -> String {
    format!("{:016x}", tcx.stable_crate_id(LOCAL_CRATE).as_u64())
}
