//! Trust: the trust-ir flip (P1 item 5) — the first "compiled from trust-ir" lane.
//!
//! For bodies whose THIR→trust-ir lowering was proven equivalent to the freshly built MIR at the
//! `mir_built` hook (derived-vs-built differential verdict `DerivedAgreed`, see
//! `trust_thir_lower::mir_differential`), `inner_optimized_mir` calls [`try_flip`] right after
//! stealing the normal body. On success the codegen path consumes MIR RE-DERIVED FROM THE
//! TRUST-IR MODULE instead of the built body.
//!
//! # Why this seam (and not the `mir_built` hook or `mir_drops_elaborated…`)
//!
//! * Borrowck must stay on the `construct_fn` MIR — the equivalence sibling — until borrow/region
//!   facts ride trust-ir (docs/DESIGN-P1-ir-inversion.md §3). Substituting at the hook would run
//!   borrowck on a derived body with erased scopes/user-type annotations.
//! * Substituting at `mir_drops_elaborated…` would also feed CTFE (`mir_for_ctfe` borrows it for
//!   const fns) and taint-tracking. `inner_optimized_mir` is exactly the codegen seam: `ensure`s
//!   `mir_for_ctfe` FIRST (from the built body), then produces the body codegen consumes — and
//!   nothing else consumes. This is also the seam §3 names (`optimized_mir` provider).
//!
//! # Pipeline parity
//!
//! The derived body leaves the shim at `MirPhase::Built`; [`advance_built_to_runtime`] replays
//! the SAME pass pipeline the built body went through between the hook and the steal — the
//! `mir_built` tail, the `mir_promoted` stage, `run_analysis_to_runtime_passes` — ending at
//! `Runtime(PostCleanup)`, the phase `inner_optimized_mir` starts from. The rest of
//! `inner_optimized_mir` (`MentionedItems`, `run_optimization_passes`, the mandatory
//! `Runtime(Optimized)` validation) then runs UNCHANGED on the flipped body. Deliberate,
//! parity-preserving deltas from the normal pipeline, all justified by the flip gates
//! (`trust_thir_lower::flip`):
//!
//! * `Lint(..)` passes are SKIPPED: lints already ran once, on the borrow-checked sibling, and
//!   `MirLint` cannot mutate the body. Re-running them on the derived body could double-emit
//!   (at the shim's coarser spans) — the one that could actually fire in-fragment,
//!   `KnownPanicsLint` inside `run_analysis_to_runtime_passes` (which IS replayed 1:1), is
//!   defused by the flip's const-trap gate instead.
//! * `lint_tail_expr_drop_order` is skipped (drop-free fragment; lint-only).
//! * `PromoteTemps` runs for parity but must produce ZERO promoted fragments (the fragment is
//!   borrow-free, so there are no candidates); a non-empty result falls back loudly — the real
//!   `promoted_mir` came from the built path.
//!
//! # Compatibility fallback and coverage honesty
//!
//! A disabled lane or a body without a recorded green Module silently keeps retained built MIR.
//! Once a recorded candidate is consumed, every structural rejection, pipeline error, or pass
//! panic (`catch_unwind`) keeps the retained body and logs a LOUD `warn!`
//! compatibility-fallback event. That preserves ordinary rustc compilation semantics, but it is
//! not evidence that the body compiled from trust-ir: direct-lane coverage only includes the
//! successful `Some(body)` cases below. Caveat for the panic arm: if a pass already emitted a
//! Bug-level diagnostic before unwinding, that diagnostic still fails the compile — the fallback
//! guarantees we never codegen a half-transformed body, not that a broken gate is cosmetically
//! invisible. The structural gate (fragment allow-list) is the actual protection; `catch_unwind`
//! is defense-in-depth. Escape hatch: `-Ztrust-ir-flip=no` (see
//! `trust_thir_lower::flip_registry`).
//!
//! Observability: one `info!` line per flipped body — grep `"compiled from trust-ir"` — with the
//! body's record-time lineage digest (`lineage`, Trust L1: the sha256-domain digest of the
//! (mini-module, callee ledger) the body was derived from, matchable against the published
//! artifact row's `lineage` field) and a
//! running per-Session crate tally (`flipped_so_far`); `warn!` per fallback. The tallies live in
//! [`rustc_session::Session`] state because a rustc_driver process may compile multiple crates.
//! Target:
//! `rustc_mir_transform::trust_ir_flip` (e.g. `RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info`).
//!
//! Incremental note: the registry is populated when `mir_built` EXECUTES. If `mir_built` is
//! green-cached, the registry is empty and the body compiles via retained built MIR. This is a
//! safe compatibility fallback, but contributes no direct-TrustIR coverage. Run equivalence
//! probes non-incrementally.

use std::panic::AssertUnwindSafe;

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{AnalysisPhase, Body, MirPhase, RuntimePhase};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use tracing::{info, warn};

use crate::required_consts::RequiredConstsVisitor;
use crate::{coverage, pass_manager as pm, promote_consts, simplify};

/// Per-compiler-invocation tallies for the event log. A rustc_driver process can create more than
/// one [`Session`], so process-global atomics would leak counts across crates and make telemetry
/// order-dependent. The Session's typed state cell also supplies the synchronization needed by
/// parallel MIR queries.
#[derive(Default)]
struct SessionFlipTelemetry {
    flipped: usize,
    fallbacks: usize,
}

impl SessionFlipTelemetry {
    fn note_flipped(&mut self) -> usize {
        self.flipped = self.flipped.saturating_add(1);
        self.flipped
    }

    fn note_fallback(&mut self) -> usize {
        self.fallbacks = self.fallbacks.saturating_add(1);
        self.fallbacks
    }
}

fn note_flipped(sess: &Session) -> usize {
    sess.with_trust_compiler_state::<SessionFlipTelemetry, _>(SessionFlipTelemetry::note_flipped)
}

fn note_fallback(sess: &Session, did: LocalDefId, reason: &str, stage: &str) {
    let fallbacks = sess
        .with_trust_compiler_state::<SessionFlipTelemetry, _>(SessionFlipTelemetry::note_fallback);
    warn!(?did, reason, stage, fallbacks, "trust-ir-flip: FALLBACK to built MIR");
}

/// Trust: attempt the flip for `did`. `Some(body)` is a `Runtime(PostCleanup)` body derived from
/// the trust-ir Module, ready for the unchanged tail of `inner_optimized_mir`; `None` means
/// "use the normal body" (silently for non-candidates, loudly for fallbacks).
pub(crate) fn try_flip<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: LocalDefId,
    normal: &Body<'tcx>,
) -> Option<Body<'tcx>> {
    // Share the exact record-time authority (both TrustIR flags, debug-info, and coverage gates)
    // instead of duplicating only `trust_ir_lower`. The registry should already be empty when any
    // gate is off; this consumer-side check is defense against future registry/call-order drift.
    if !trust_thir_lower::flip_registry::flip_session_enabled(tcx) {
        return None;
    }

    let (body, asserts, lineage) = match trust_thir_lower::flip::derive_flip_body(tcx, did, normal)
    {
        trust_thir_lower::flip::FlipAttempt::NotCandidate => return None,
        trust_thir_lower::flip::FlipAttempt::Rejected { reason } => {
            note_fallback(tcx.sess, did, &reason, "gate");
            return None;
        }
        trust_thir_lower::flip::FlipAttempt::Derived { body, asserts, lineage } => {
            (body, asserts, lineage)
        }
    };

    // Advance Built -> Runtime(PostCleanup) with the same passes the built sibling saw.
    // catch_unwind is defense-in-depth only (see module docs); the structural gate is what
    // makes the pipeline total over the admitted fragment.
    let advanced = std::panic::catch_unwind(AssertUnwindSafe(move || {
        let mut body = body;
        advance_built_to_runtime(tcx, &mut body).map(|()| body)
    }));

    match advanced {
        Ok(Ok(body)) => {
            let flipped = note_flipped(tcx.sess);
            // Trust (L1): `lineage` is the record-time digest of the (mini-module, callee
            // ledger) this body was derived from — the value that matches the registry
            // object and the published artifact row. Always present: `record_green`
            // declines digest-less bodies, so no flip event can fire without it.
            info!(
                ?did,
                asserts,
                lineage = %lineage,
                flipped_so_far = flipped,
                "trust-ir-flip: compiled from trust-ir"
            );
            Some(body)
        }
        Ok(Err(reason)) => {
            note_fallback(tcx.sess, did, &reason, "pipeline");
            None
        }
        Err(_panic) => {
            note_fallback(
                tcx.sess,
                did,
                "derived-body pass PANICKED (caught); if a Bug diagnostic was already emitted \
                 this compile still fails, but no derived code is emitted",
                "pipeline-panic",
            );
            None
        }
    }
}

/// Trust (CTFE flip lane): attempt the flip for a const/associated-const ITEM on the `mir_for_ctfe`
/// seam. Mirrors [`try_flip`], but gates on the const context BEFORE `derive_flip_body` (which
/// `take`s the registry entry): a const FN must NOT be consumed here — it is a CODEGEN-seam
/// candidate (flipped there as an ordinary runtime fn, wave-I), and its `mir_for_ctfe` (const-eval)
/// body stays BUILT. Consuming its entry here would starve the codegen seam (the split of
/// const-eval-on-built vs runtime-on-derived is benign: `DerivedAgreed` ⇒ derived ≡ built).
/// Const ITEMS (`Const{..}`) reach the const-eval interpreter through THIS body only, so one seam
/// flips them with no double-consumption. `Static(_)`
/// passes the pre-gate for forward-compatibility but is not yet recorded in the registry (→ `take`
/// returns `None` → `NotCandidate`) and is separately rejected by `derive_flip_body`. The returned
/// body is `Runtime(PostCleanup)` — exactly the phase `inner_mir_for_ctfe` feeds to `CtfeLimit`
/// (which never optimizes), so `advance_built_to_runtime` is reused verbatim. A rejection or
/// pipeline failure preserves the retained built body and does not count as direct-TrustIR
/// coverage. A false equivalence can still bake a wrong constant; the on/off differential is the
/// detection backstop, and detectable UB is caught harder here (interpreter hard error).
pub(crate) fn try_flip_ctfe<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: LocalDefId,
    normal: &Body<'tcx>,
) -> Option<Body<'tcx>> {
    if !trust_thir_lower::flip_registry::flip_session_enabled(tcx) {
        return None;
    }
    // Trust (adversarial review CONFIRMED-1): mirror the codegen seam's taint guard
    // (`inner_optimized_mir` returns the built body when `tainted_by_errors` is set, BEFORE
    // `try_flip`). A const item can be green at the `mir_built` hook yet become tainted LATER
    // (const-qualif / borrowck / WF), and the derived body is born UNtainted (the shim never sets
    // `tainted_by_errors`) — so without this guard the interpreter would evaluate a body derived from
    // error-containing THIR instead of bailing at `load_mir`'s taint short-circuit. Not a
    // released-artifact hole (taint carries an `ErrorGuaranteed` ⇒ a diagnostic already fired ⇒ the
    // compile fails regardless), but we must not diverge: skip the flip, let `CtfeLimit` run on the
    // built body. NOTE (review SUSPECTED-1): the derived body also bypasses
    // `remap_mir_for_const_eval_select` — identical to the shipping codegen seam. Sound because NO
    // flipped body (const ITEM or, as of wave-I, const fn) can contain a `const_eval_select` call:
    // it is a `Call` to an intrinsic NOT on the shim's flip allowlist, so any body mentioning it
    // fails to lower clean → never `DerivedAgreed` → never registered. Left as inherited trust base.
    if normal.tainted_by_errors.is_some() {
        return None;
    }
    // Only const/static ITEMS are candidates on this seam. A const FN or any non-const body must
    // NOT reach `derive_flip_body` here — that would `take` an entry the codegen seam owns. Gate
    // BEFORE take. (The set matches `inner_mir_for_ctfe`'s steal arm exactly.)
    match tcx.hir_body_const_context(did) {
        Some(rustc_hir::ConstContext::Const { .. } | rustc_hir::ConstContext::Static(_)) => {}
        _ => return None,
    }

    let (body, asserts, lineage) = match trust_thir_lower::flip::derive_flip_body(tcx, did, normal)
    {
        trust_thir_lower::flip::FlipAttempt::NotCandidate => return None,
        trust_thir_lower::flip::FlipAttempt::Rejected { reason } => {
            note_fallback(tcx.sess, did, &reason, "ctfe-gate");
            return None;
        }
        trust_thir_lower::flip::FlipAttempt::Derived { body, asserts, lineage } => {
            (body, asserts, lineage)
        }
    };

    // Advance Built -> Runtime(PostCleanup), the phase the const-eval interpreter consumes (this
    // seam never runs the optimization tail — `CtfeLimit` is the only pass after the hook).
    let advanced = std::panic::catch_unwind(AssertUnwindSafe(move || {
        let mut body = body;
        advance_built_to_runtime(tcx, &mut body).map(|()| body)
    }));

    match advanced {
        Ok(Ok(body)) => {
            let flipped = note_flipped(tcx.sess);
            // Trust (L1): same lineage attestation as the codegen seam — see `try_flip`.
            info!(
                ?did,
                asserts,
                lineage = %lineage,
                flipped_so_far = flipped,
                "trust-ir-flip: CTFE compiled from trust-ir"
            );
            Some(body)
        }
        Ok(Err(reason)) => {
            note_fallback(tcx.sess, did, &reason, "ctfe-pipeline");
            None
        }
        Err(_panic) => {
            note_fallback(
                tcx.sess,
                did,
                "derived const body pass PANICKED (caught); built MIR const-evaluated instead",
                "ctfe-pipeline-panic",
            );
            None
        }
    }
}

/// Replay the built body's pass pipeline over the derived body: `mir_built` tail →
/// `mir_promoted` stage → `run_analysis_to_runtime_passes` (the same public entry the normal
/// path uses). Lint passes skipped (see module docs). Errors are returned, never emitted.
fn advance_built_to_runtime<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) -> Result<(), String> {
    if body.phase != MirPhase::Built {
        return Err(format!("derived body at {:?}, expected Built", body.phase));
    }

    // Stage A — the `mir_built` provider tail (its Lint passes skipped).
    pm::run_passes(tcx, body, &[&simplify::SimplifyCfg::Initial], None, pm::Optimizations::Allowed);

    // Stage B — the `mir_promoted` stage. `required_consts` must be computed before promotion,
    // exactly as `mir_promoted` does; `InstrumentCoverage` is in the list for parity but is
    // disabled by its own `is_enabled` (the flip is session-gated off under coverage).
    RequiredConstsVisitor::compute_required_consts(body);
    let promote_pass = promote_consts::PromoteTemps::default();
    pm::run_passes(
        tcx,
        body,
        &[&promote_pass, &simplify::SimplifyCfg::PromoteConsts, &coverage::InstrumentCoverage],
        Some(MirPhase::Analysis(AnalysisPhase::Initial)),
        pm::Optimizations::Allowed,
    );
    let promoted = promote_pass.promoted_fragments.into_inner();
    if !promoted.is_empty() {
        // The real promoted bodies came from the built path; a promotion here means the gate
        // admitted a borrow — fail closed.
        return Err(format!(
            "PromoteTemps produced {} fragment(s) on the derived body",
            promoted.len()
        ));
    }

    // Stage C — analysis → runtime, shared verbatim with the normal path.
    crate::run_analysis_to_runtime_passes(tcx, body);

    if body.phase != MirPhase::Runtime(RuntimePhase::PostCleanup) {
        return Err(format!("phase advance ended at {:?}", body.phase));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
