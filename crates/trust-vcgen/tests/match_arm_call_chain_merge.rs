//! REAL-MIR matrix for a `match` arm whose value is computed through a CALL.
//!
//! ```text
//! pub enum Kind { Word, Set, Deferred }
//! pub struct E { pub kind: Kind, pub index: u32, pub len: u32, pub big: u64 }
//! pub fn through_match(e: &E, words: u64) -> bool {
//!     let span = match e.kind {
//!         Kind::Word => 1,
//!         Kind::Set => u64::from(e.len) + 1,
//!         Kind::Deferred => return false,
//!     };
//!     u64::from(e.index) + span > words                  // line 9
//! }
//! pub fn through_option(e: &E, words: u64) -> bool {
//!     let span = match e.kind {
//!         Kind::Word => Some(1),
//!         Kind::Set => Some(u64::from(e.len) + 1),
//!         Kind::Deferred => None,
//!     };
//!     if let Some(span) = span {
//!         return u64::from(e.index) + span > words;      // line 18
//!     }
//!     false
//! }
//! // `..._unbounded`: the same two functions with the `Set` arm spelled
//! // `u64::from(e.len) + e.big` (lines 28 and 37).
//! pub fn cast_arm_control(e: &E, words: u64) -> bool {  // the already-supported shape
//!     let span = match e.kind {
//!         Kind::Word => 1,
//!         Kind::Set => e.len as u64 + 1,                  // no `Call` hop
//!         Kind::Deferred => return false,
//!     };
//!     e.index as u64 + span > words                      // line 47
//! }
//! ```
//!
//! The `Set` arm lowers to a CHAIN, not a single block:
//!
//! ```text
//! bb0: _4 = discriminant((*_1).0); switchInt(_4) -> [0: bb4, 1: bb3, 2: bb2, otherwise: bb1]
//! bb3: _6 = (*_1).2; _5 = <u64 as From<u32>>::from(move _6) -> [return: bb5, ..]
//! bb5: _7 = AddWithOverflow(_5, 1); assert(!_7.1) -> [success: bb6, ..]
//! bb6: _3 = move _7.0; goto bb7                         // the join
//! ```
//!
//! The single-switch branch-merge recogniser admitted a value arm that hangs off
//! the switch directly, or through exactly ONE checked-arithmetic `Assert`. The
//! `Call` hop in front of the `Assert` made it decline the whole join, so `span`
//! reached the final add as a FREE variable bounded only by its `u64` type, and
//! the add — which cannot overflow, `u32::MAX + (u32::MAX + 1) < 2^64` — was
//! REFUTED with `span = 2^64 - 2^32 + 1` (measured on stage1 `7be75e9a80`; the
//! same row is `tla-model-ir` `model.rs` `check_vars_and_pool`). The control
//! `direct` (`let span = u64::from(e.len) + 1;` with no match) proved.
//!
//! The `Option` rows need a second fact. The `None` arm gives the payload no
//! value, so there is no total merge for it; the PARTIAL merge states each
//! defining arm's value under that arm's exact route guard, and the VARIANT
//! ROUTE (`guards::switch_join_variant_arm_definitions`) states, at the `Some`
//! arm of `if let Some(span)`, that only the `Some`-building merge arms can have
//! run. Measured with each lever alone: neither proves the `Option` row.
//!
//! The `_unbounded` rows are the adversarial half: `span` may be any `u64`
//! there (`e.big = u64::MAX - u32::MAX` with `e.len = u32::MAX` makes the arm
//! itself succeed and the final add overflow at `e.index = 1`), so the final add
//! must stay NOT proved — a merge that let the hull of the arms' bounds leak a
//! bound no arm proves would turn these into false proofs.
//!
//! Every fixture is the compiler's OWN extracted verification input, captured
//! verbatim with `trustc --edition 2021 --crate-type lib -Ztrust-verify=on
//! -Ztrust-dump=mir:<dir> match_arm_call_chain.rs` (stage1 `7be75e9a80`, default
//! optimisation) and edited only by minifying the JSON and rewriting the
//! absolute span path to `<dump-root>/match_arm_call_chain.rs`.

use trust_types::{
    Formula, LocalDecl, Place, Rvalue, SourceSpan, Statement, Ty, VcKind, VerifiableFunction,
    VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const BOUNDED: &str = include_str!("fixtures/match_arm_call_chain_bounded_mir.json");
const OPTION_BOUNDED: &str = include_str!("fixtures/match_arm_call_chain_option_bounded_mir.json");
const UNBOUNDED: &str = include_str!("fixtures/match_arm_call_chain_unbounded_mir.json");
const OPTION_UNBOUNDED: &str =
    include_str!("fixtures/match_arm_call_chain_option_unbounded_mir.json");
const CAST_CONTROL: &str = include_str!("fixtures/match_arm_call_chain_cast_control_mir.json");

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

/// VC generation and the solver search both run on this thread; libtest's
/// default 2 MiB is not enough for the recursive `Formula` walks.
const SOLVER_STACK_BYTES: usize = 32 * 1024 * 1024;

/// The `ArithmeticOverflow` obligations at source line `line` with their
/// verdicts, decided by the real in-process ay.
fn overflow_rows_at(func: VerifiableFunction, line: u32) -> Vec<(Formula, VerificationResult)> {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs: Vec<_> = trust_vcgen::generate_vcs(&func)
                .into_iter()
                .filter(|vc| {
                    matches!(vc.kind, VcKind::ArithmeticOverflow { .. })
                        && vc.location.line_start == line
                })
                .collect();
            assert!(
                !vcs.is_empty(),
                "{}: no overflow obligation at line {line}; an absent obligation is not a \
                 discharged one",
                func.name
            );
            let router = test_router::deterministic_test_router();
            let results = router.verify_all(&vcs);
            vcs.into_iter().map(|vc| vc.formula).zip(results.into_iter().map(|(_, r)| r)).collect()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn assert_proved(json: &str, line: u32, why: &str) {
    for (formula, verdict) in overflow_rows_at(load(json), line) {
        assert!(
            matches!(verdict, VerificationResult::Proved { .. }),
            "line {line}: the add cannot overflow because {why}; got {verdict:?}\n\
             formula: {formula:?}"
        );
    }
}

/// `!Proved` rather than `Failed`: `Unknown`/`Timeout` also leave the obligation
/// undischarged, which is the soundness property these rows pin.
fn assert_not_proved(func: VerifiableFunction, line: u32, witness: &str) {
    for (_, verdict) in overflow_rows_at(func, line) {
        assert!(
            !matches!(verdict, VerificationResult::Proved { .. }),
            "line {line}: the add OVERFLOWS at {witness}; proving it is a FALSE PROOF; \
             got {verdict:?}"
        );
    }
}

/// The verdict's variant, for comparing two rows' outcome CLASS.
fn class(verdict: &VerificationResult) -> &'static str {
    match verdict {
        VerificationResult::Proved { .. } => "Proved",
        VerificationResult::Failed { .. } => "Failed",
        VerificationResult::Unknown { .. } => "Unknown",
        VerificationResult::Timeout { .. } => "Timeout",
        _ => "other",
    }
}

/// The plain-`match` row lands on the footing of the already-supported
/// cast-arm shape: same merge, same verdict.
///
/// It is not asserted `Proved` here because the in-process ay alone does not
/// certify EITHER row today: its UNSAT is withheld by the mandatory strict
/// self-check (`[stop-item:generic-theory-lemma]`, the disequality split the
/// merge's `else` guard `_4 != 0` needs). The compiler discharges the control
/// through its full-verifier lane; the stage-1 measurement of this row is
/// recorded in `docs/DECISION_QUEUE.md` (MATCH-ARM-CALL-CHAIN). What this test
/// pins is the vcgen half: the counterexample is gone, the arm value is the
/// call-chain's `_5 + 1` (no longer a free `span`), and the verdict class is the
/// control's.
#[test]
fn a_call_then_checked_add_arm_keeps_its_bound_across_the_join() {
    let rows = overflow_rows_at(load(BOUNDED), 9);
    let control = overflow_rows_at(load(CAST_CONTROL), 47);
    for (formula, verdict) in &rows {
        assert!(
            !matches!(verdict, VerificationResult::Failed { .. }),
            "line 9: span is 1 or u64::from(u32) + 1, so index + span <= 2^33 has no \
             counterexample; got {verdict:?}\nformula: {formula:?}"
        );
        let rendered = format!("{formula:?}");
        assert!(
            rendered.contains("Eq(Var(\"span#s4_0_s6_0\", Int), Add(Var(\"_5\", Int), Int(1)))"),
            "the call-chain arm's value `_5 + 1` must reach the join; formula: {rendered}"
        );
        for (_, control_verdict) in &control {
            assert_eq!(
                class(verdict),
                class(control_verdict),
                "the call-chain arm must decide like the cast-arm control"
            );
        }
    }
}

#[test]
fn a_call_then_checked_add_arm_keeps_its_bound_through_an_option_join() {
    assert_proved(
        OPTION_BOUNDED,
        18,
        "the Some payload is 1 or u64::from(u32) + 1, so index + span <= 2^33",
    );
}

#[test]
fn an_unbounded_call_chain_arm_still_refutes_the_add() {
    assert_not_proved(
        load(UNBOUNDED),
        28,
        "kind = Set, len = u32::MAX, big = u64::MAX - u32::MAX, index = 1",
    );
}

#[test]
fn an_unbounded_call_chain_arm_still_refutes_the_add_through_an_option_join() {
    assert_not_proved(
        load(OPTION_UNBOUNDED),
        37,
        "kind = Set, len = u32::MAX, big = u64::MAX - u32::MAX, index = 1",
    );
}

/// A `Call` hop may write anything a callee can reach. With the switch selector
/// `_4` mutably borrowed (`_99 = &mut _4` before the switch), the callee in the
/// `Set` chain could rewrite it, so an `Ite` keyed on `_4` could name the wrong
/// arm: the merge must DECLINE, and `span` is free again — REFUTED, not merely
/// undecided (the merged row is `Unknown`, so `!Proved` would not see the gate).
///
/// Two gates decline this shape, and the row pins the outcome, not one gate:
/// the Call block's write set already names the escaped `_4` (the hop write
/// check), and the explicit selector gate (`chain_has_call`: a bare, never
/// mutably borrowed local) refuses it again. MEASURED: with the explicit gate
/// disabled this row still passes; the explicit gate is the defence for a
/// selector the write set cannot name (a projected place behind a pointer).
#[test]
fn a_reachable_selector_declines_the_call_chain_merge() {
    let mut func = load(BOUNDED);
    let selector = 4;
    assert!(
        matches!(
            &func.body.blocks[0].terminator,
            trust_types::Terminator::SwitchInt { discr, .. }
                if matches!(discr, trust_types::Operand::Move(p) | trust_types::Operand::Copy(p)
                    if p.local == selector && p.projections.is_empty())
        ),
        "fixture drift: bb0 must switch on `_4`"
    );
    let borrow = func.body.locals.len();
    let selector_ty = func.body.locals[selector].ty.clone();
    func.body.locals.push(LocalDecl {
        index: borrow,
        ty: Ty::Ref { mutable: true, inner: Box::new(selector_ty) },
        name: None,
    });
    let switch_block = &mut func.body.blocks[0];
    let at = switch_block.stmts.len();
    switch_block.stmts.insert(
        at,
        Statement::Assign {
            place: Place::local(borrow),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(selector) },
            span: SourceSpan::default(),
        },
    );
    for (formula, verdict) in overflow_rows_at(func, 9) {
        assert!(
            matches!(verdict, VerificationResult::Failed { .. }),
            "line 9: with `_4` reachable by the callee the merge must decline and the add \
             stay refuted; got {verdict:?}\nformula: {formula:?}"
        );
    }
}
