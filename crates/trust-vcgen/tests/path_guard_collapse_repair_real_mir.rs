//! REAL-ARTIFACT regression guard for the SECOND path-guard collapse — the
//! GLOBAL STEP BUDGET — and for the row class the first repair's scope missed.
//!
//! `v2_build_path_guard_map` degrades in two ways, and both leave a block with
//! ONE UNGUARDED path whose term lowers to an unconditional `true`:
//!
//! ```text
//! MODE 1  the block was reached by more than MAX_PATHS_PER_BLOCK routes
//! MODE 2  the walk outran its global step budget  ->  EVERY block at once
//! ```
//!
//! `tests/coroutine_resume_state_global_fact_real_mir.rs` covers mode 1. This
//! file covers mode 2, and it covers it on a NON-coroutine body as well, because
//! the budget-trip return is not coroutine-specific: it collapses every function
//! whose path walk is large enough.
//!
//! Both fixtures are the compiler's OWN extracted verification input, captured
//! verbatim with `-Ztrust-dump=mir:<dir>`:
//!
//! ```rust,ignore
//! // path_budget_nonasync_merged_unreachable
//! pub fn f(b0: bool, .., b12: bool, x: Option<u8>) -> u16 {
//!     let mut t: u16 = 0;
//!     if b0 { t = t.wrapping_add(1); }   // .. thirteen times
//!     t | match x { Some(v) => v as u16, None => 0 }
//! }
//!
//! // path_budget_async_sentinel
//! pub async fn f(a0: Option<u8>, .., a12: Option<u8>) -> u16 {
//!     let mut t: u16 = 0;
//!     t = t | match a0 { Some(v) => v as u16, None => 0 };  // .. thirteen times
//!     t
//! }
//! ```
//!
//! Neither can fault. Every match is exhaustive, `|` on `u16` cannot overflow,
//! and `wrapping_add` is total.
//!
//! # The two defects this pins
//!
//! **The budget-trip collapse.** The `steps > cap` arm returned before the
//! mode-1 repair ran, so the same false REFUTATION survived one step further
//! out — a cliff a body crosses by growing one more match, with nothing about
//! the program changed. Where each fixture sits relative to that cliff, and how
//! wide it is, are asserted in
//! `trust_vcgen::generate::path_guard_collapse_tests::walk_arithmetic`. The
//! non-async fixture is the same cliff for a plain `fn`, which is what pins the
//! scope: this is not a coroutine bug.
//!
//! **The repair's scope.** Mode 1's repair was gated on
//! `Terminator::Unreachable`, justified as "for any other obligation the
//! collapse is only imprecision, since the row keeps its own violation
//! condition". The FIRST half of that is false for rustc's `ResumedAfter*`
//! coroutine sentinel: `safety.rs` builds its row from
//! `v2_assert_failure_formula(const false, expected: true)`, which IS the
//! constant `true` — so the path condition is the row's entire content, exactly
//! as for `Unreachable`, and it refutes under collapse for exactly the same
//! reason. The SECOND half is true, and is what fixes the scope: a row with its
//! own violation condition needs no restored path condition, and giving it one
//! multiplies its formula by the block's in-degree, which demotes a genuine
//! `Mul` overflow from REFUTED to `Unknown` (see
//! `tests/path_guard_collapse_cost_real_mir.rs`).
//!
//! So the repair covers every collapsed block's CONTENT-FREE rows, and the class
//! is recognised structurally by `v2_violation_is_content_free` — from what a
//! row's formula says, not from a list of row kinds a new kind can fall off.
//! Where no sound in-edge disjunction exists at all, the COLLAPSE INVARIANT
//! declines the row (an explicit `PathConditionDegraded` proof gap) rather than
//! shipping an unconditional accusation.

use trust_types::{
    Terminator, VcKind, VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/data/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("MIR fixture {path} must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("MIR fixture {path} must deserialize: {e}"))
}

fn nonasync() -> VerifiableFunction {
    load("path_budget_nonasync_merged_unreachable")
}

fn async_sentinel() -> VerifiableFunction {
    load("path_budget_async_sentinel")
}

fn refuted(vcs: &[VerificationCondition]) -> Vec<String> {
    let router = test_router::deterministic_test_router();
    router
        .verify_all(vcs)
        .into_iter()
        .filter(|(_, result)| matches!(result, VerificationResult::Failed { .. }))
        .map(|(vc, _)| format!("{:?}", vc.kind))
        .collect()
}

fn without_extractor_preconditions(mut func: VerifiableFunction) -> VerifiableFunction {
    func.preconditions.clear();
    func
}

fn block_mut(func: &mut VerifiableFunction, id: usize) -> &mut trust_types::BasicBlock {
    func.body
        .blocks
        .iter_mut()
        .find(|b| b.id.0 == id)
        .unwrap_or_else(|| panic!("fixture must have bb{id}"))
}

/// THE REGRESSION, plain `fn`. A correct non-async function whose path walk
/// outruns the step budget may not be refuted. This is the case the coroutine
/// premise cannot rescue — there is no resume selector here at all — so it
/// isolates the path-guard repair from every coroutine fact.
#[test]
fn a_correct_non_async_body_past_the_step_budget_is_never_refuted() {
    let func = nonasync();
    assert!(
        trust_types::coroutine_resume_state_contract(&func.body).is_none(),
        "the fixture's value is that it is NOT a coroutine: the budget-trip return \
         collapses every function, and this is the one that says so"
    );
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(!vcs.is_empty(), "fixture must still emit obligations");
    assert_eq!(refuted(&vcs), Vec::<String>::new());
}

/// THE REGRESSION, recognized `async fn` resume body past the budget. Both the
/// merged `Unreachable` row and the `ResumedAfter*` sentinel `Assertion` row are
/// `Bool(true)`-bodied, so both are decided entirely by the path condition.
#[test]
fn a_correct_async_body_past_the_step_budget_is_never_refuted() {
    let func = async_sentinel();
    assert!(
        trust_types::coroutine_resume_state_contract(&func.body).is_some(),
        "fixture must be a recognized resume body"
    );
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(!vcs.is_empty(), "fixture must still emit obligations");
    assert_eq!(refuted(&vcs), Vec::<String>::new());
}

/// D1b, named. `safety.rs`'s `AssertMessage::ResumedAfter*` arm emits this row
/// with the formula `v2_assert_failure_formula(const false, expected: true)` —
/// the constant `true`. Its ONLY content is therefore the path condition, which
/// is exactly the property the earlier repair's `Terminator::Unreachable` gate
/// was justified by denying ("for any other obligation the collapse is only
/// imprecision, since the row keeps its own violation condition"). Assert it by
/// NAME, so a future re-narrowing of the repair's scope cannot pass this file by
/// proving the `Unreachable` row alone.
#[test]
fn the_resumed_after_sentinel_row_is_present_and_survives_the_budget_trip() {
    fn is_sentinel_row(vc: &VerificationCondition) -> bool {
        matches!(&vc.kind, VcKind::Assertion { message }
            if message.contains("coroutine protocol assert: ResumedAfter"))
    }
    let func = async_sentinel();
    let vcs = trust_vcgen::generate_vcs(&func);
    let sentinel_rows: Vec<&VerificationCondition> =
        vcs.iter().filter(|vc| is_sentinel_row(vc)).collect();
    assert!(
        !sentinel_rows.is_empty(),
        "the body must still EMIT a refutable ResumedAfter* row — the premise \
         conditions rows, it never prunes one: {:?}",
        vcs.iter().map(|vc| format!("{:?}", vc.kind)).collect::<Vec<_>>()
    );
    // The row's own violation core is a BOOLEAN TAUTOLOGY — `assert(const false,
    // expected: true)` fires when `cond != expected`, which
    // `v2_assert_failure_formula` spells `Not(Bool(false))`. It constrains no
    // program variable, so everything that decides this row comes from the
    // conjoined facts and the PATH CONDITION. That is exactly why a collapsed
    // path guard accuses it, and if the core ever stops being a tautology the
    // D1b rationale has to be re-derived rather than assumed.
    fn contains_tautological_core(f: &trust_types::Formula) -> bool {
        use trust_types::Formula;
        match f {
            Formula::Bool(true) => true,
            Formula::Not(inner) => matches!(inner.as_ref(), Formula::Bool(false)),
            other => other.children().into_iter().any(contains_tautological_core),
        }
    }
    assert!(
        sentinel_rows.iter().all(|vc| contains_tautological_core(&vc.formula)),
        "the row's violation core must be the tautology: {:?}",
        sentinel_rows.iter().map(|vc| &vc.formula).collect::<Vec<_>>()
    );
    let router = test_router::deterministic_test_router();
    for (vc, result) in router.verify_all(&vcs) {
        if is_sentinel_row(&vc) {
            assert!(
                !matches!(result, VerificationResult::Failed { .. }),
                "the sentinel row is decided by its path condition alone, so a \
                 collapsed path guard accuses it unconditionally: {:?}",
                vc.kind
            );
        }
    }
}

/// ATTRIBUTION. Both bodies stay unrefuted with the extractor's preconditions
/// removed, so the result rides on facts derived in this crate rather than on a
/// hypothesis that arrived in the serialized input.
#[test]
fn the_repair_is_derived_not_inherited() {
    for fixture in [nonasync(), async_sentinel()] {
        let vcs = trust_vcgen::generate_vcs(&without_extractor_preconditions(fixture));
        assert_eq!(refuted(&vcs), Vec::<String>::new());
    }
}

/// NEGATIVE CONTROL — real UB past the budget still REFUTES. Dropping the `Some`
/// arm of the `Option` match routes `d == 1`, a value the type permits, straight
/// into the merged `Unreachable`. The restored condition is a DISJUNCTION of the
/// in-edge guards, so an in-edge a live value can actually take leaves the row
/// satisfiable — exactly as it must. Without this the repair could be blessing
/// UB and the tests above would not notice.
#[test]
fn a_reachable_unreachable_past_the_budget_still_refutes() {
    for fixture in [nonasync(), async_sentinel()] {
        let mut func = without_extractor_preconditions(fixture);
        // The first non-entry `SwitchInt` that reads a `Discriminant` — the
        // `Option` match — located structurally rather than by a pinned id.
        let switch = func
            .body
            .blocks
            .iter()
            .find(|b| {
                b.id.0 != 0
                    && matches!(b.terminator, Terminator::SwitchInt { .. })
                    && b.stmts.iter().any(|s| {
                        matches!(
                            s,
                            trust_types::Statement::Assign {
                                rvalue: trust_types::Rvalue::Discriminant(_),
                                ..
                            }
                        )
                    })
            })
            .map(|b| b.id.0)
            .expect("fixture matches on an enum");
        let Terminator::SwitchInt { targets, .. } = &mut block_mut(&mut func, switch).terminator
        else {
            panic!("located block must be the enum switch");
        };
        let before = targets.len();
        targets.retain(|(value, _)| *value != 1);
        assert_eq!(targets.len(), before - 1, "the mutation must actually drop an arm");
        let refuted = refuted(&trust_vcgen::generate_vcs(&func));
        assert!(
            refuted.iter().any(|kind| kind.contains("Unreachable")),
            "a reachable `Unreachable` is real UB and must never be blessed: {refuted:?}"
        );
    }
}

/// NEGATIVE CONTROL — an UNGUARDED in-edge defeats the in-edge summary, as it
/// must. Retargeting a `Goto` at the merged `Unreachable` makes it reachable
/// unconditionally; the disjunction is then `true`.
///
/// That is POSITIVE information, not absence, and the distinction is the reason
/// the collapse invariant does not weaken UB detection: `Unconditional` says the
/// block IS reached, so nothing is restored AND nothing is declined — the row
/// stays REFUTED. Folding this case together with "no summary available" would
/// bless real UB here.
#[test]
fn an_unguarded_edge_into_the_unreachable_block_still_refutes() {
    for fixture in [nonasync(), async_sentinel()] {
        let mut func = without_extractor_preconditions(fixture);
        let target = func
            .body
            .blocks
            .iter()
            .find(|b| matches!(b.terminator, Terminator::Unreachable))
            .map(|b| b.id)
            .expect("the fixture has a merged unreachable block");
        let goto = func
            .body
            .blocks
            .iter()
            .find(|b| matches!(b.terminator, Terminator::Goto(_)))
            .map(|b| b.id.0)
            .expect("the fixture has a Goto block");
        block_mut(&mut func, goto).terminator = Terminator::Goto(target);
        let refuted = refuted(&trust_vcgen::generate_vcs(&func));
        assert!(
            refuted.iter().any(|kind| kind.contains("Unreachable")),
            "an unconditional edge into the block leaves it genuinely reachable: \
             {refuted:?}"
        );
    }
}

/// The repair conditions rows; it never prunes one. Same anti-silence property
/// the mode-1 fix had to keep.
#[test]
fn the_repair_never_adds_or_removes_an_obligation() {
    for fixture in [nonasync as fn() -> VerifiableFunction, async_sentinel] {
        let vcs = trust_vcgen::generate_vcs(&fixture());
        let kinds: Vec<String> = vcs.iter().map(|vc| format!("{:?}", vc.kind)).collect();
        assert!(
            kinds.iter().any(|k| k.contains("Unreachable")),
            "the collapsed body must still carry its `Unreachable` obligation: {kinds:?}"
        );
    }
}
