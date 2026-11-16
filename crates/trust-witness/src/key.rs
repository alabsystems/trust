//! The witness key.
//!
//! v1 ships the SOUND default key (PLAN.md §5): schema version + the root's
//! own body hash + a whole-crate local identity (every HIR owner's hash, the
//! local source files, the whole `[TRACKED]` options fingerprint including the
//! lint levels but not the per-run freshness values, and the stable crate id;
//! the metadata-based SVH does not exist yet at typeck) + all upstream SVHs.
//! A hit therefore
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
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
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
    //
    // Upstream 1.101: `tcx.crate_hash(LOCAL_CRATE)` panics before metadata
    // encoding (the metadata-based SVH is only computed while encoding), and
    // this key is computed during typeck. The local component is therefore
    // the same HIR-based identification upstream itself uses when metadata
    // is not encoded (`crate_hash`'s else branch): the commutative combine
    // of every HIR owner's fingerprint, the session's dep-tracking hash,
    // the stable crate id, and the remapped local source-file identities.
    // Any intra-crate HIR change moves some owner fingerprint, so the
    // whole-crate gate is preserved; upstream crates still enter by SVH.
    let local_env: Fingerprint = {
        let hir_body_hash = rustc_middle::hir::map::compute_hir_hash(tcx);
        let mut source_file_names: Vec<_> = tcx
            .sess
            .source_map()
            .files()
            .iter()
            .filter(|source_file| source_file.cnum == LOCAL_CRATE)
            .map(|source_file| source_file.stable_id)
            .collect();
        source_file_names.sort_unstable();
        tcx.with_stable_hashing_context(|mut hcx| {
            let mut stable_hasher = StableHasher::new();
            hir_body_hash.stable_hash(&mut hcx, &mut stable_hasher);
            source_file_names.stable_hash(&mut hcx, &mut stable_hasher);
            // The whole `[TRACKED]` fingerprint (docs/TYPECK_MOONSHOT.md, A3) less the two
            // per-invocation freshness values (`Options::witness_tracking_hash`). This was
            // `dep_tracking_hash(true)`, the crate-hash subset, which leaves out the
            // `[TRACKED_NO_CRATE_HASH]` options, `lint_opts` and `lint_cap` among them. The mint
            // gate admits a root only when its typeck emitted no diagnostic under the minting
            // compile's lint levels, so that key replayed a root minted under `--cap-lints
            // allow` or default levels into a compile run with `-D <lint>` and lost that typeck
            // lint: the warm compile succeeded where a cold one failed.
            tcx.trust_witness_options_hash().stable_hash(&mut hcx, &mut stable_hasher);
            tcx.stable_crate_id(LOCAL_CRATE).stable_hash(&mut hcx, &mut stable_hasher);
            stable_hasher.finish()
        })
    };
    let env = environment_fingerprint(
        crate::schema::SCHEMA_VERSION,
        local_env,
        tcx.crates(()).iter().map(|cnum| tcx.crate_hash(*cnum).as_u128()),
    );
    let (e0, e1) = env.split();

    Some(format!(
        "{}_{}_{:016x}{:016x}",
        root_dph.0.to_hex(),
        owner_hash.to_hex(),
        e0.as_u64(),
        e1.as_u64()
    ))
}

// Keep this input order exact: the helper makes the epoch's domain separation
// testable with identical local/upstream identities, without changing the key.
fn environment_fingerprint(
    schema: &str,
    local_env: Fingerprint,
    upstream_hashes: impl IntoIterator<Item = u128>,
) -> Fingerprint {
    let mut h = StableHasher::new();
    h.write(schema.as_bytes());
    let (l0, l1) = local_env.split();
    h.write_u64(l0.as_u64());
    h.write_u64(l1.as_u64());
    for hash in upstream_hashes {
        h.write_u128(hash);
    }
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retired_schema_is_a_distinct_key_domain_with_identical_environment() {
        let local_env = Fingerprint::ZERO;
        let upstream = [0x1122_3344_5566_7788_99aa_bbcc_ddee_ff00, 0x1020_3040];
        let retired = environment_fingerprint("trust.typeck-witness.v6", local_env, upstream);
        let current = environment_fingerprint(crate::schema::SCHEMA_VERSION, local_env, upstream);
        assert_ne!(
            retired, current,
            "retired witnesses must miss with every other input held fixed"
        );
    }
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
