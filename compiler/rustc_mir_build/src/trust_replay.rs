//! Trust (typeck-moonshot P1, Phase 3): the CHECKED witness-replay hook body.
//!
//! Registered as the `trust_witness_try_replay` hook (rustc_middle) so the
//! `typeck`-query wrapper in `rustc_hir_typeck` can delegate reconstruct +
//! re-intern + check without a static edge on THIR-build. FAIL-SAFE by
//! construction: every miss / decode / reintern / check failure returns `None`,
//! and the caller falls through to real typeck. The linear checker is the
//! MANDATORY authority — a decoded-but-unchecked result is never returned
//! (CHECKED, not TRUSTED).

use rustc_data_structures::fx::FxHashSet;
use rustc_hir::HirId;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeckResults};
use rustc_span::def_id::LocalDefId;

use crate::thir::cx::trust_build_check_thir;

/// Env-gated diagnostic: emit the replay outcome per root to stderr when
/// `TRUST_WITNESS_STATS` is set. Off by default (no effect on stderr, so
/// byte-identity validation is unaffected); a validation harness sets it and
/// counts ACCEPT / REJECT / MISS lines to prove firing.
fn stat(outcome: &str, def_id: LocalDefId) {
    if std::env::var_os("TRUST_WITNESS_STATS").is_some() {
        eprintln!("TRUST_REPLAY {outcome} {def_id:?}");
    }
}

/// Try to replay `typeck(def_id)` from a stored witness. `def_id` is a typeck
/// ROOT (the caller guards this; we re-check defensively). Returns the
/// arena-allocated candidate iff the checker accepts, else `None`.
pub(crate) fn replay_hook<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<&'tcx TypeckResults<'tcx>> {
    // Only a typeck root is replayable — children fold into their root in
    // `typeck_with_inspect`, and the witness/key is per-root.
    if tcx.typeck_root_def_id_local(def_id) != def_id {
        return None;
    }

    // Router (AUTO mode only): replay pays a fixed decode + check-THIR + checker
    // cost, so it only wins on bodies big enough that fresh typeck would cost more.
    // Skip small bodies (cheap O(1) HIR node-count gate) BEFORE any store I/O, so
    // the managed lane never slows a trivial body — it just falls through to normal
    // typeck. An explicit `-Ztrust-witness=replay:<dir>` replays every stored root.
    if tcx.trust_witness_replay_router_skip(def_id) {
        return None;
    }

    // Forest-checking (increment 1): the bodies sharing this root's TypeckResults
    // that the checker must walk — the root + its value-inline-const children. A
    // closure/coroutine child (or any owner mismatch) => `None` => MISS, because
    // increment 1 does not yet round-trip captures/upvars. `precise=false` here:
    // this is the TRUST (replay) path, which stays closure-free; closure admission
    // is confined to the never-trusted precise/parity shadow-mint.
    let Some(walk) = trust_witness::forest_const_walk_set(tcx, def_id, false) else {
        stat("MISS-child-body", def_id);
        return None;
    };

    // Load the packed per-crate store and pick this root's witness by the sound
    // whole-environment key. Any absence => clean miss => real typeck.
    let dir = tcx.trust_witness_replay_dir()?;
    // This trust path uses the SOUND whole-SVH key. In precise mode the caller
    // (typeck_root) never invokes this hook — the precise key is measured, not
    // trusted, via `parity_check_hook`.
    let key = trust_witness::witness_key(tcx, def_id)?;
    let Some(store) = trust_witness::store::read(&dir, &trust_witness::store_stem(tcx)) else {
        stat("MISS-nostore", def_id);
        return None;
    };
    let Some(bytes) = store.get(&key) else {
        stat("MISS-nokey", def_id);
        return None;
    };

    // Decode + re-intern into an OWNED `TypeckResults`. Any `DefPathHash -> None`,
    // any exotic-grammar type, any structural decode error => `None`, never panic.
    let decoded = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        trust_witness::decode_and_reintern(tcx, def_id, bytes)
    }));
    let Some(results) = decoded.unwrap_or(None) else {
        stat("MISS-decode", def_id);
        return None;
    };

    // Same `&'tcx` shape writeback produces (arena declares `[decode]
    // typeck_results`); mirrors `writeback.rs`'s `tcx.arena.alloc(..)`.
    let candidate: &'tcx TypeckResults<'tcx> = tcx.arena.alloc(results);

    // Decoder output must itself remain inside the narrow enabled set. This is
    // a replay-side authority check, not merely a mint optimization: arbitrary
    // store bytes must not populate a lossy/default-only field the checker does
    // not independently re-derive. `precise=false`: this is the TRUSTED replay
    // path, which must stay inside the reconstruction-faithful set (closures /
    // non-Rust-ABI sigs excluded); the precise/parity lane never reaches here.
    if !trust_witness::mintable(candidate, false) {
        stat("MISS-enabled-set", def_id);
        return None;
    }

    // Coverage: every method/operator pick must be keyed inside a body the forest
    // walk covers (the root + inline-const children). A pick keyed elsewhere is
    // installed-but-unwalkable => reject.
    if !trust_witness::picks_all_in_walked_bodies(tcx, candidate, &walk) {
        stat("MISS-childpick", def_id);
        return None;
    }

    // Forest-check EVERY body sharing this root's TypeckResults: build a throwaway
    // check-THIR for each (not the `thir_body` query — its cache is untouched) and
    // run the linear checker, accumulating one combined outcome and the UNION of
    // the pick FnDef tys the checker actually re-resolved. The root's check-THIR is
    // kept for the single-build lookaside install; child THIRs are discarded
    // (`thir_body(child)` rebuilds from the shared candidate — one extra build).
    //
    // Rank-5 fail-safe (audit 2026-07-22): a corrupt/stale witness, or an
    // unencoded-field access in a child body, can `bug!` during a check-THIR build
    // or a checker-internal layout_of/normalize BEFORE the accept gate runs. Catch
    // any such unwind and treat it as a clean MISS -> real typeck, so a bad .twit
    // never aborts the compile. On the normal ACCEPT path nothing panics, so this
    // is transparent (byte-identity of a valid replay is unaffected).
    let built = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut rederived: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        let mut combined = trust_witness::checker::CheckOutcome {
            checked: 0,
            weak: 0,
            unchecked: 0,
            failed: 0,
            trusted_weak: 0,
        };
        let mut root_thir_expr = None;
        for &b in &walk {
            let (thir, expr) = trust_build_check_thir(tcx, b, candidate).ok()?;
            let env = ty::TypingEnv::post_analysis(tcx, b.to_def_id());
            let o = trust_witness::checker::check(tcx, &thir, env, &mut rederived);
            combined.checked += o.checked;
            combined.weak += o.weak;
            combined.unchecked += o.unchecked;
            combined.failed += o.failed;
            combined.trusted_weak += o.trusted_weak;
            if b == def_id {
                root_thir_expr = Some((thir, expr));
            }
        }
        root_thir_expr.map(|(t, e)| (t, e, combined, rederived))
    }));
    let Some((thir, expr, outcome, rederived)) = built.unwrap_or(None) else {
        stat("MISS-thir-or-panic", def_id);
        return None;
    };

    // Covered-set gate (forest-checking completeness backstop): every
    // `type_dependent_defs` AssocFn pick's re-materialized FnDef ty must be in the
    // union of tys the checker actually RE-RESOLVED (`try_resolve`) across the
    // forest — else a pick was installed but never re-derived (e.g. a pick lowered
    // to a bare fn-value the walk never reached). SUBSET, not equality: `rederived`
    // also holds free-fn/ctor calls. `mintable` admits only ground monomorphic
    // AssocFn picks, so `want` is the exact ground FnDef the corresponding Call
    // carries.
    let coverage_ok = candidate.type_dependent_defs().items_in_stable_order().into_iter().all(
        |(local_id, res)| {
            let did = match res {
                Ok((DefKind::AssocFn, did)) => *did,
                _ => return true,
            };
            let args = candidate
                .node_args_opt(HirId { owner: candidate.hir_owner, local_id })
                .unwrap_or_else(|| tcx.mk_args(&[]));
            let want = tcx.erase_and_anonymize_regions(Ty::new_fn_def(tcx, did, args));
            rederived.iter().any(|t| tcx.erase_and_anonymize_regions(*t) == want)
        },
    );

    // MANDATORY authority: every walked body accepts (the summed failed / unchecked
    // / pick-trusting-weak counts are 0 iff each body's are) AND every admitted pick
    // was re-derived. Accept => return the candidate; else fall through to real typeck.
    if trust_witness::checker::accepts(&outcome) && coverage_ok {
        stat("ACCEPT", def_id);
        // P1 follow-on: stash the already-checked ROOT THIR so `thir_body` reuses it
        // (single THIR build on the replay path). Only reached on ACCEPT.
        tcx.trust_witness_thir_install(def_id, thir, expr);
        Some(candidate)
    } else {
        if std::env::var_os("TRUST_WITNESS_STATS").is_some() {
            eprintln!(
                "TRUST_REPLAY REJECT {def_id:?} failed={} unchecked={} trusted_weak={} checked={} coverage={coverage_ok}",
                outcome.failed, outcome.unchecked, outcome.trusted_weak, outcome.checked
            );
        }
        None
    }
}

/// Trust (typeck-moonshot A1-A3): the precise-key shadow-mint PARITY measurement.
/// Reports whether the precise-keyed stored witness for `def_id` byte-matches
/// `encode_root(real)` — i.e. whether the edit-loop precise key retrieved a witness
/// consistent with what real typeck just produced. `Some(true)` = MATCH,
/// `Some(false)` = DIVERGE (a negative-information hole: the precise key hit a stale
/// witness a prior compile minted), `None` = no witness / not applicable / real not
/// encodable. PURE OBSERVATION: never decodes-and-installs, never returns a
/// candidate — the caller always uses real typeck's result, so this can never
/// miscompile. Inert unless `-Ztrust-witness-precise` is set.
pub(crate) fn parity_check_hook<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    real: &'tcx TypeckResults<'tcx>,
) -> Option<bool> {
    if !tcx.trust_witness_precise() || tcx.typeck_root_def_id_local(def_id) != def_id {
        return None;
    }
    let dir = tcx.trust_witness_replay_dir()?;
    // `real` is the just-computed TypeckResults, so the precise key never re-queries typeck.
    let key = trust_witness::precise_witness_key(tcx, def_id, real)?;
    let store = trust_witness::store::read(&dir, &trust_witness::store_stem(tcx))?;
    let bytes = store.get(&key)?;
    let real_bytes = trust_witness::encode_root(tcx, real)?;
    Some(bytes.as_slice() == real_bytes.as_slice())
}
