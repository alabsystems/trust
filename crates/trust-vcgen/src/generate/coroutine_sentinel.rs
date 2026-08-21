// trust_vcgen/generate/coroutine_sentinel.rs: the refutation-lane prover for
// rustc's compiler-inserted `ResumedAfter{Return,Panic,Drop}` protocol
// sentinels.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// WHY THIS EXISTS. `generate::safety` deliberately emits NO obligation for the
// three `ResumedAfter*` assert messages, and `generate_full_assert_refutation_vcs`
// walks only `Terminator::Call` panic sites — but rustc lowers a sentinel as a
// `Terminator::Assert`, never a call. So NOTHING in the pipeline ever asked the
// solver about a sentinel: the coroutine body's whole-function panic-freedom
// row was stamped `Proved` by the INTERPROCEDURAL discharge, whose stated
// soundness premise enumerates panic sites as "(a) an obligation in `results`,
// (b) a `Terminator::Call`" — and a sentinel is NEITHER. For a zero-await
// resume body (no calls at all) that rule is VACUOUSLY true, so the row was a
// proof that never looked at the sentinel.
//
// WHAT THIS PROVES, EXACTLY. One candidate per sentinel:
//
//     path-feasibility(sentinel block)  ∧  selector ∈ live_states
//
// On the refutation lane SAT = refuted, UNSAT = proved. UNSAT is therefore a
// claim about the BODY alone: "no execution that enters this resume body in a
// LIVE resume state reaches the executor-protocol sentinel". It is NOT, and
// must never be read as, a proof that the executor honors that precondition —
// that premise is about the CALLER. It is discharged nowhere here; the compiler
// publishes it as the `contract:coroutine-resume-state` row (verified modulo
// callers) and charges every in-bundle poll/resume call site a real, honestly
// unprovable obligation for it (`COROUTINE_RESUME_PRECONDITION_PREFIX`).
//
// This is a SEPARATE public entry point rather than a hunk inside
// `assert_refutation.rs` so the sentinel lane can be reviewed, tested and
// reverted on its own, and so the general refutation lane keeps exactly its
// current candidate set.

use trust_types::fx::FxHashSet;
use trust_types::{
    AssertMessage, BlockId, ConstValue, Formula, GuardCondition, Operand, Terminator, VcKind,
    VerifiableFunction, VerificationCondition,
};

use super::StmtVersionCtx;
use super::path_defs::version_rename_at;
use super::safety::{v2_build_path_guard_map, v2_formula_with_path_guards};
use super::semantic_guard::func_exceeds_vcgen_budget;
use crate::guards;

/// The sentinel text the marker description carries, mirroring the trust-ir
/// bridge's `format_assert_message` spelling for exactly the three
/// executor-protocol messages. `None` for every other assert message — this
/// lane mints candidates ONLY for the compiler-generated `ResumedAfter*`
/// sentinels, never for a user assert (whose text is user-controlled and must
/// never reach an authenticated marker channel).
fn coroutine_sentinel_message_text(msg: &AssertMessage) -> Option<&'static str> {
    match msg {
        AssertMessage::ResumedAfterReturn => Some("resumed after return"),
        AssertMessage::ResumedAfterPanic => Some("resumed after panic"),
        AssertMessage::ResumedAfterDrop => Some("resumed after drop"),
        _ => None,
    }
}

/// Does `func`'s body carry any compiler-generated `ResumedAfter*` protocol
/// sentinel? The compiler uses this to keep the INTERPROCEDURAL panic-freedom
/// rule — which enumerates panic sites as obligations-plus-calls, and so
/// provably cannot see a sentinel `Terminator::Assert` — away from bodies whose
/// panic surface it does not enumerate.
#[must_use]
pub fn body_has_coroutine_protocol_sentinel(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|block| {
        matches!(&block.terminator, Terminator::Assert { msg, .. }
            if coroutine_sentinel_message_text(msg).is_some())
    })
}

/// Trust (coroutine resume-state contract): one refutation candidate per
/// compiler-inserted `ResumedAfter{Return,Panic,Drop}` sentinel of a body whose
/// resume ENTRY dispatch `trust_types::coroutine_resume_state_contract`
/// recognizes.
///
/// The MESSAGE is the shared bridge marker
/// (`coroutine_resume_contract_obligation_description`), so the compiler's
/// publish seam can recognize a PROVED row as the visible sentinel proof: it
/// parses the state set back out and requires it to equal the bridge's
/// authenticated module evidence.
///
/// NON-VACUITY. A WRONG live-state set makes the sentinel arm's own guard
/// satisfiable under the precondition (live `{0, 1}` admits `selector == 1`,
/// the RETURNED arm), so the candidate is SAT → REFUTED → a red row. A contract
/// must fail loudly when its state set is wrong, never pass because nobody
/// looked.
///
/// FAIL-CLOSED on every shape doubt — an unrecognized body, an entry selector
/// that is not the whole-local the recognizer named, a sentinel that is not a
/// DIRECT successor of the entry dispatch, a sentinel block with no path-guard
/// entry, a saturated/degraded path-guard set (any UNGUARDED path, whose
/// unconditional `true` term would make the candidate trivially SAT), a path
/// carrying more than the one entry-dispatch guard, or a feasibility formula
/// mentioning no variable at all or ANY variable other than the constrained
/// selector — yields NO candidate for that sentinel. Withholding a candidate
/// can only drop a refutation and a proof, never manufacture either.
///
/// WHY THE DIRECT-SUCCESSOR GATE. `v2_build_path_guard_map` enumerates
/// syntactic paths and conjoins only their BRANCH conditions; it does not model
/// whether an intermediate block terminates. On a multi-edge path that
/// over-approximates reachability, and an over-approximated reachable set makes
/// a SAT witness SPURIOUS — a FALSE REFUTATION (a red build on a correct
/// program). Restricting candidates to sentinels that are direct targets of the
/// recognized entry `SwitchInt` — which is exactly the shape rustc's
/// `insert_panic_block` mints, and exactly the shape the recognizer audits
/// before subtracting a discriminant from the live set — makes the single
/// remaining guard the EXACT reachability condition, so SAT and UNSAT are both
/// faithful.
#[must_use]
pub fn coroutine_sentinel_refutation_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    // AUTHORITY: the live-state set comes from the ONE pure recognizer the
    // bridge and the compiler both use — never re-derived here, so the three
    // ends cannot drift. Checked FIRST because it is a cheap structural scan
    // that declines every non-coroutine body, keeping this lane off the hot
    // path of `refute_full_assert_obligations` (which calls it per function).
    let Some(contract) = trust_types::coroutine_resume_state_contract(&func.body) else {
        return Vec::new();
    };
    if crate::validate_function(func).is_err() {
        return Vec::new();
    }
    // verifier-perf: same whole-function gate the refutation lane applies, for
    // the same reason (`StmtVersionCtx::build` / path-guard machinery explodes
    // on an over-budget recursive-datatype body). DROP-ONLY, so fail-closed.
    let _gen_work_scope = crate::gen_work_scope();
    if func_exceeds_vcgen_budget(func) {
        return Vec::new();
    }
    let Some(entry) = func.body.blocks.first() else {
        return Vec::new();
    };
    let Terminator::SwitchInt { discr, targets, .. } = &entry.terminator else {
        return Vec::new();
    };
    // (belt) the dispatch operand must be the whole-local selector the
    // recognizer named; anything else and we do not know what we would be
    // constraining. Decline.
    let selector_ok = matches!(
        discr,
        Operand::Copy(place) | Operand::Move(place)
            if place.projections.is_empty() && place.local == contract.discr_local
    );
    if !selector_ok {
        return Vec::new();
    }

    let sv = StmtVersionCtx::build(func);
    let guard_paths_map = v2_build_path_guard_map(func);

    // The exported precondition, spelled through the SAME `guard_to_formula`
    // path the dispatch's own path guards go through and versioned at the SAME
    // point (`v2_formula_with_path_guards` versions each guard at its source
    // block's terminal statement index) — so the precondition's selector symbol
    // unifies with the guard's BY CONSTRUCTION. A hand-rolled `Eq(Var, Int)`
    // could differ in sort/name and be silently name-disjoint (inert), which
    // would leave the candidate UNCONSTRAINED and refute every well-formed
    // async body.
    let entry_terminal = entry.stmts.len();
    let live_terms: Vec<Formula> = contract
        .live_states
        .iter()
        .map(|state| {
            let guard = guards::guard_to_formula(
                func,
                &GuardCondition::SwitchIntMatch { discr: discr.clone(), value: *state },
            );
            version_rename_at(&guard, &sv, func, entry.id, entry_terminal)
        })
        .collect();
    let precondition = match live_terms.len() {
        // `coroutine_resume_contract_states_are_valid` guarantees non-empty, so
        // the 0 arm is unreachable; decline rather than emit an empty `Or`
        // (which would be `false` and make EVERY sentinel vacuously UNSAT).
        0 => return Vec::new(),
        1 => match live_terms.into_iter().next() {
            Some(term) => term,
            None => return Vec::new(),
        },
        _ => Formula::Or(live_terms),
    };
    // The symbols the precondition actually constrains. The feasibility formula
    // may mention NOTHING else: a stray free variable would be UNCONSTRAINED
    // and could be picked to satisfy the formula — a false refutation of a
    // well-formed async body.
    let constrained: FxHashSet<String> = precondition.free_variables().into_iter().collect();
    // Sentinel blocks that are DIRECT targets of the recognized entry dispatch
    // (see the direct-successor rationale on this function's doc comment).
    let entry_arm_targets: FxHashSet<BlockId> =
        targets.iter().map(|(_, target)| *target).collect();

    let mut out = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Assert { cond, expected, msg, span, .. } = &block.terminator else {
            continue;
        };
        // Exactly rustc's `insert_panic_block` sentinel shape — the SAME shape
        // `trust_types`' recognizer audits when it lets the arm's discriminant
        // be subtracted from the live set. A conditional or non-constant assert
        // is NOT a sentinel and keeps its ordinary treatment.
        if !matches!(cond, Operand::Constant(ConstValue::Bool(false))) || !*expected {
            continue;
        }
        let Some(sentinel) = coroutine_sentinel_message_text(msg) else {
            continue;
        };
        if !entry_arm_targets.contains(&block.id) {
            continue;
        }
        let Some(paths) = guard_paths_map.get(&block.id) else { continue };
        // Every path into the sentinel must be exactly ONE guard sourced at the
        // entry dispatch. `v2_build_path_guard_map` degrades to a single EMPTY
        // guard list when a block saturates (`MAX_PATHS_PER_BLOCK`) or its
        // global step budget trips, and an empty guard list lowers to the
        // unconditional `true` term — which would make the candidate trivially
        // SAT and REFUTE a well-formed async body (a FALSE red, and a `Failed`
        // row claiming a violation that does not exist). A longer path is the
        // over-approximation hazard the doc comment describes. Decline both.
        if paths.is_empty()
            || paths.iter().any(|guards| {
                guards.len() != 1 || guards.first().is_none_or(|(src, _)| *src != entry.id)
            })
        {
            continue;
        }
        let feasibility = v2_formula_with_path_guards(func, &sv, paths, Formula::Bool(true));
        let free = feasibility.free_variables();
        // The feasibility must MENTION the selector and NOTHING ELSE: a formula
        // with no free variable carries no reachability condition at all (same
        // trivially-SAT hazard as above), and a stray free variable is
        // UNCONSTRAINED here. Both decline.
        if free.is_empty() || !free.iter().all(|v| constrained.contains(v)) {
            continue;
        }
        out.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: trust_types::assumption::coroutine_resume_contract_obligation_description(
                    &contract.live_states,
                    sentinel,
                ),
            },
            function: func.name.clone().into(),
            location: span.clone(),
            formula: Formula::And(vec![precondition.clone(), feasibility]),
            contract_metadata: None,
            obligation: None,
        });
    }
    out
}
