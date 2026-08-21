// Trust (coroutine resume-state contract): the `-full` assert-refutation lane's
// prover for rustc's compiler-inserted `ResumedAfter{Return,Panic,Drop}`
// protocol sentinels.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// The property under test is NON-VACUITY, and it has two halves that must both
// hold or the published `contract:coroutine-resume-state` row would be
// meaningless:
//   * RIGHT live set -> the sentinel candidate is UNSAT (ay `Proved`), i.e. a
//     genuine proof that no execution honoring the exported precondition
//     reaches the sentinel — and the VC carries the shared bridge MARKER
//     message, which is what makes the proof VISIBLE to the compiler's
//     `rows_exhibit_coroutine_sentinel_proof` gate;
//   * WRONG live set -> the candidate is SAT (ay `Failed`), i.e. REFUTED/red.
//     A contract whose state set is wrong must fail loudly; it must never pass
//     because nobody looked. The wrong set here is produced through the REAL
//     recognizer (a dispatch whose live state 3 arm targets the
//     ResumedAfterReturn sentinel), not by hand-building a formula, so the test
//     exercises the same seam production does.

use trust_types::UnwindEdge;
use trust_types::{
    AssertMessage, BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

use super::coroutine_sentinel::coroutine_sentinel_refutation_vcs;

/// `fn f::{closure#0}(self: Pin<&mut {coroutine}>, cx) -> Poll<u16>` — the
/// rustc lowering of a ZERO-AWAIT `async fn` resume body:
/// `bb0: _3 = discriminant((*_1)); switchInt(_3) -> [0: body, 1: resumed-after-
/// return sink, 2: resumed-after-panic sink, otherwise: unreachable]`. Mirrors
/// `trust_types`' own `zero_await_resume_body` recognizer fixture so both ends
/// of the contract are pinned on the same MIR shape.
fn zero_await_resume_fn() -> VerifiableFunction {
    let frame_ty = Ty::Ref {
        mutable: true,
        inner: Box::new(Ty::Coroutine {
            name: "fixture::f::{closure#0}".into(),
            upvars: vec![Ty::u8()],
        }),
    };
    // rustc emits the protocol sink as an always-failing assert that SELF-LOOPS.
    let sentinel = |id: usize, msg: AssertMessage| BasicBlock {
        id: BlockId(id),
        stmts: vec![],
        terminator: Terminator::Assert {
            cond: Operand::Constant(ConstValue::Bool(false)),
            expected: true,
            msg,
            target: BlockId(id),
            span: SourceSpan::default(),
            unwind: UnwindEdge::Unreachable,
        },
    };
    VerifiableFunction {
        name: "fixture::f::{closure#0}".into(),
        def_path: "fixture::f::{closure#0}".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u16(), name: None },
                LocalDecl { index: 1, ty: frame_ty, name: Some("self".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: None },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Discriminant(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        }),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2)), (2, BlockId(3))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: true,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                sentinel(2, AssertMessage::ResumedAfterReturn),
                sentinel(3, AssertMessage::ResumedAfterPanic),
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Unreachable },
            ],
            arg_count: 2,
            return_ty: Ty::u16(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The marker-parsed live-state set of every coroutine-sentinel candidate in
/// `vcs`, in emission order. A candidate that is NOT marker-described is not a
/// sentinel candidate and is excluded — the gate the compiler applies too.
fn sentinel_live_state_sets(vcs: &[trust_types::VerificationCondition]) -> Vec<Vec<u128>> {
    vcs.iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::Assertion { message } => {
                trust_types::assumption::parse_coroutine_resume_contract_obligation_description(
                    message,
                )
                .map(|(states, _)| states)
            }
            _ => None,
        })
        .collect()
}

fn sentinel_texts(vcs: &[trust_types::VerificationCondition]) -> Vec<String> {
    vcs.iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::Assertion { message } => {
                trust_types::assumption::parse_coroutine_resume_contract_obligation_description(
                    message,
                )
                .map(|(_, sentinel)| sentinel.to_string())
            }
            _ => None,
        })
        .collect()
}

#[test]
fn zero_await_resume_body_mints_marker_described_sentinel_candidates() {
    let vcs = coroutine_sentinel_refutation_vcs(&zero_await_resume_fn());
    // One per `ResumedAfter*` sentinel block (return + panic), each naming the
    // recognized live set {0} in the EXACT shared marker spelling the bridge
    // stamps — this is what makes the later PROVED row visible to the
    // compiler's sentinel-proof gate.
    assert_eq!(sentinel_live_state_sets(&vcs), vec![vec![0u128], vec![0u128]]);
    // The sentinel text mirrors the bridge's `format_assert_message`.
    assert_eq!(sentinel_texts(&vcs), vec!["resumed after return", "resumed after panic"]);
}

#[test]
fn plain_body_mints_no_sentinel_candidate() {
    // Anti-overreach control: the same lane over a body the resume-state
    // recognizer DECLINES (no exhaustiveness certificate) must mint no
    // marker-described candidate at all — the marker is an authenticated
    // channel and may never be stamped without the recognizer.
    let mut func = zero_await_resume_fn();
    let Terminator::SwitchInt { exhaustive_enum_unreachable, .. } =
        &mut func.body.blocks[0].terminator
    else {
        unreachable!("fixture entry terminator is a SwitchInt")
    };
    *exhaustive_enum_unreachable = false;
    assert!(sentinel_live_state_sets(&coroutine_sentinel_refutation_vcs(&func)).is_empty());
}

#[test]
fn a_sentinel_reachable_by_more_than_the_entry_dispatch_is_declined() {
    // The candidate's soundness rests on the sentinel's reachability being the
    // ENTRY DISPATCH ARM ALONE: one guard, on the one variable the exported
    // precondition constrains. Here live state 0 routes through a data
    // conditional that can ALSO reach the ResumedAfterReturn sink, so the
    // feasibility formula is a multi-edge path carrying a free variable the
    // precondition says nothing about. Emitting the candidate anyway would let
    // the solver pick that free value and REFUTE — a FALSE red — so the lane
    // DECLINES (fail-closed: no sentinel proof is visible, the pre-existing
    // `assumption:coroutine` row + strict abort stands).
    let mut func = zero_await_resume_fn();
    let Terminator::SwitchInt { targets, .. } = &mut func.body.blocks[0].terminator else {
        unreachable!("fixture entry terminator is a SwitchInt")
    };
    targets[0] = (0, BlockId(5));
    func.body.blocks.push(BasicBlock {
        id: BlockId(5),
        stmts: vec![],
        terminator: Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(2)),
            targets: vec![(0, BlockId(2))],
            otherwise: BlockId(1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    });
    // The ResumedAfterReturn sink (now data-reachable) is DROPPED; its sibling,
    // still reachable only from the reserved POISONED arm, keeps its candidate
    // — the decline is per-sentinel, not a blanket shutdown of the lane. With
    // one candidate against an evidence count of two, the compiler's
    // count-equality gate then withholds the contract row anyway (fail-closed).
    assert_eq!(
        sentinel_texts(&coroutine_sentinel_refutation_vcs(&func)),
        vec!["resumed after panic"]
    );
}

#[test]
fn right_live_set_makes_every_sentinel_candidate_unsat() {
    use trust_router::{InProcessAyBackend, VerificationBackend};
    let backend = InProcessAyBackend::new();
    let vcs = coroutine_sentinel_refutation_vcs(&zero_await_resume_fn());
    let sentinel_vcs: Vec<&trust_types::VerificationCondition> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::Assertion { message }
                if trust_types::assumption::
                    parse_coroutine_resume_contract_obligation_description(message).is_some())
        })
        .collect();
    assert_eq!(sentinel_vcs.len(), 2);
    for vc in sentinel_vcs {
        assert!(backend.can_handle(vc), "ay must admit the sentinel candidate: {:?}", vc.kind);
        let result = backend.verify(vc);
        // In THIS lane UNSAT = proved: reaching the sentinel requires the
        // selector to be a RESERVED state (1 or 2), which the exported
        // precondition `state ∈ {0}` contradicts.
        assert!(
            matches!(result, trust_types::VerificationResult::Proved { .. }),
            "the sentinel is unreachable under the exported precondition, got {result:?}"
        );
    }
}

#[test]
fn wrong_live_set_refutes_the_sentinel_candidate() {
    use trust_router::{InProcessAyBackend, VerificationBackend};
    // NON-VACUITY. A dispatch whose LIVE (non-reserved) state 3 arm targets the
    // `ResumedAfterReturn` sentinel is exactly a contract whose exported state
    // set is WRONG: it claims state 3 is a resumable state while resuming there
    // provably panics with the executor-protocol message. The recognizer still
    // accepts the body (the reserved arms are genuine sentinels), so the live
    // set really is {0, 3} — and the candidate must come out SAT/REFUTED, i.e.
    // red, instead of quietly certifying a false contract.
    let mut func = zero_await_resume_fn();
    let Terminator::SwitchInt { targets, .. } = &mut func.body.blocks[0].terminator else {
        unreachable!("fixture entry terminator is a SwitchInt")
    };
    targets.push((3, BlockId(2)));
    let vcs = coroutine_sentinel_refutation_vcs(&func);
    assert_eq!(sentinel_live_state_sets(&vcs), vec![vec![0u128, 3], vec![0u128, 3]]);
    let backend = InProcessAyBackend::new();
    // The ResumedAfterReturn sentinel (bb2) is now reachable from the live
    // state 3, so its candidate is SAT.
    let returned = vcs
        .iter()
        .find(|vc| match &vc.kind {
            VcKind::Assertion { message } => message.ends_with("resumed after return"),
            _ => false,
        })
        .expect("the ResumedAfterReturn candidate must exist");
    let result = backend.verify(returned);
    assert!(
        matches!(result, trust_types::VerificationResult::Failed { .. }),
        "a wrong live state set must REFUTE the sentinel, got {result:?}"
    );
    // The ResumedAfterPanic sentinel (bb3) is still reachable only from the
    // reserved state 2, so it stays proved — the refutation is targeted, not a
    // blanket failure of the lane.
    let panicked = vcs
        .iter()
        .find(|vc| match &vc.kind {
            VcKind::Assertion { message } => message.ends_with("resumed after panic"),
            _ => false,
        })
        .expect("the ResumedAfterPanic candidate must exist");
    assert!(
        matches!(backend.verify(panicked), trust_types::VerificationResult::Proved { .. }),
        "the still-unreachable sentinel must stay proved"
    );
}
