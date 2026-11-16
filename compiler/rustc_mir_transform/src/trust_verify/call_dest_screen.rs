//! Trust (D5-A, 2026-09-24): the compiler's census of a body's calls into
//! same-crate free `fn`s, for the negative-only call-destination screen of
//! `trust_vcgen::GenericRefutationScope`.
//!
//! ## The false refutation this closes
//!
//! ```text
//! pub fn guard(bit: u32) -> bool { bit < 64 }
//! pub fn shift_via_guard(x: u64, bit: u32) -> Option<u64> {
//!     if !guard(bit) { return None; }
//!     Some(x >> bit)
//! }
//! ```
//!
//! Measured on stage-1 (wave 0, `a8c853de6f`): `[shift:right] FAILED
//! (ay-in-process); counterexample: _3 = true, … bit = 64`. `_3` is
//! `guard(bit)`'s result; no summary models it, so it is a free variable of
//! the query and the solver CHOSE `true` for `bit = 64` — a value `guard`
//! never returns there. The inline twin (`if !(bit < 64)`) proves. The row is
//! a model of the formula, not a run: an unmodeled call result must read
//! UNKNOWN, never as a refutation.
//!
//! `havoc_decline` (trust-vcgen) does not reach it: it screens only FOREIGN
//! callees and integer destinations, and it treats a path guard as pinning.
//!
//! ## What this module decides, and what it does not
//!
//! It decides WHICH callees are screened, from `TyCtxt` facts about the callee
//! `DefId` — never from a rendered string:
//!
//! * the callee is a direct `FnDef` call (`const_fn_def`), LOCAL, of
//!   `DefKind::Fn` (a free function: no trait or inherent method, no closure,
//!   no constructor), not a foreign item, and has no generic parameters at all
//!   (`generics_of(..).count() == 0`), so the identity instantiation is the only
//!   one and trust-vcgen's `CalleeIdentity` on the call names it exactly.
//!
//! It also hands over the body's contract-summary DB itself. trust-vcgen
//! decides from it which callees' injected `ensures` DETERMINE the result
//! (`SummaryDatabase::postcondition_pinning_callees`), and re-asks the
//! injector's call-site gate at each call; only such a destination is left
//! alone. (Trust, 2026-09-28: the census used to hand over every INJECTING
//! name, so `requires b <= a ensures result <= a` counted as pinning `r` and
//! `p_falsefail::dead_else` reported a contract-level model as FAILED.)
//!
//! It decides NOTHING about proof. The screen can only replace an ay/interval
//! `Failed` with a held `Unknown` (`GENERIC_REFUTATION_HELD_PREFIX`), which
//! `result_is_held_assert_refutation` keeps a fail-closed coverage gap with no
//! runtime-check tolerance. A build that errored still errors; an empty census
//! (any non-compiler caller) is the pre-D5 behaviour.

use rustc_hir::def::DefKind;
use rustc_middle::mir::{Body, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefId, LOCAL_CRATE};

/// Build the census for `body`. `summaries` must be the DB this body's VCs are
/// generated with (`vc_summaries`), so "pinned by a summary" is judged against
/// the summaries generation actually saw.
pub(super) fn local_call_dest_screen<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    summaries: &trust_vcgen::SummaryDatabase,
) -> trust_vcgen::LocalCallDestScreen {
    let local_crate = tcx.stable_crate_id(LOCAL_CRATE).as_u64();
    let mut screened = Vec::new();
    for bb in body.basic_blocks.iter() {
        let Some(term) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::Call { func: callee_op, .. } = &term.kind else {
            continue;
        };
        let Some((def_id, args)) = callee_op.const_fn_def() else {
            continue;
        };
        if screened_callee(tcx, def_id, args.is_empty()) {
            screened.push((local_crate, def_id.index.as_u32()));
        }
    }
    // Trust (2026-09-28): the DB, not its injecting names — see the module doc.
    trust_vcgen::LocalCallDestScreen::new(screened, summaries)
}

/// Whether a direct call to `def_id` (with `args_empty` generic arguments) is a
/// same-crate, non-generic, non-foreign free function.
fn screened_callee(tcx: TyCtxt<'_>, def_id: DefId, args_empty: bool) -> bool {
    def_id.is_local()
        && args_empty
        && matches!(tcx.def_kind(def_id), DefKind::Fn)
        && !tcx.is_foreign_item(def_id)
        && tcx.generics_of(def_id).count() == 0
}
