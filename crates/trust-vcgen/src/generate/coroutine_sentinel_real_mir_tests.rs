// Trust (coroutine resume-state contract): the sentinel prover against REAL
// compiler-extracted MIR, not a hand-built body.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// `coroutine_sentinel_tests.rs` pins the lane on a synthetic resume body. This
// file pins it on the body rustc ACTUALLY produces for the falsification row
// `tests/trust-falsification/proved/async_zero_await_widen.rs`, captured with
//
//     trustc --edition 2021 --crate-type lib -Cpanic=abort \
//            -Ztrust-policy=certify -Ztrust-dump=mir:<dir> \
//            async_zero_await_widen.rs
//
// and committed verbatim (only the absolute source path in the spans is
// relativized) as
// `fixtures/coroutine_resume/async_zero_await_widen__f__closure0.json`.
//
// WHY THE REAL BODY MATTERS: that falsification row stayed RED while every
// synthetic test was green, so nothing but production MIR settles whether the
// recognizer and this lane fire in vivo. The real body differs from the
// synthetic one in exactly the ways that could have broken either: the `self`
// parameter is `Pin<&mut {coroutine}>` (an ADT wrapping the reference, so the
// frame place is reached through a `Deref` projection off a *different* local),
// three unrelated statements precede the discriminant read in the entry block,
// the dispatch has only TWO arms ({0 -> body, 1 -> ResumedAfterReturn}) because
// a `-Cpanic=abort` zero-await coroutine has no POISONED arm, and the sentinel
// block SELF-LOOPS.

use trust_types::{AssertMessage, BlockId, Terminator, VcKind, VerifiableFunction};

use super::coroutine_sentinel::coroutine_sentinel_refutation_vcs;

/// The committed real-MIR dump of `async_zero_await_widen::f::{closure#0}`.
fn real_resume_body() -> VerifiableFunction {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("coroutine_resume")
        .join("async_zero_await_widen__f__closure0.json");
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    let func: VerifiableFunction = serde_json::from_str(&json)
        .unwrap_or_else(|error| panic!("failed to parse {}: {error}", path.display()));
    assert_eq!(func.def_path, "async_zero_await_widen::f::{closure#0}");
    func
}

/// The marker-parsed (live states, sentinel text) of every sentinel candidate.
fn sentinel_markers(func: &VerifiableFunction) -> Vec<(Vec<u128>, String)> {
    coroutine_sentinel_refutation_vcs(func)
        .iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::Assertion { message } => {
                trust_types::assumption::parse_coroutine_resume_contract_obligation_description(
                    message,
                )
                .map(|(states, sentinel)| (states, sentinel.to_string()))
            }
            _ => None,
        })
        .collect()
}

fn sentinel_candidates(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    coroutine_sentinel_refutation_vcs(func)
        .into_iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::Assertion { message }
                if trust_types::assumption::
                    parse_coroutine_resume_contract_obligation_description(message).is_some())
        })
        .collect()
}

#[test]
fn real_zero_await_resume_dispatch_is_recognized_with_live_set_zero() {
    let func = real_resume_body();
    let contract = trust_types::coroutine_resume_state_contract(&func.body)
        .expect("rustc's real zero-await resume dispatch must be recognized");
    // Certified case set {0, 1} minus the reserved RETURNED=1, whose arm is the
    // verified `ResumedAfterReturn` panic sentinel.
    assert_eq!(contract.live_states, vec![0u128]);
    // The selector is the entry discriminant temp: neither an argument nor a
    // frame field.
    assert!(contract.discr_local > func.body.arg_count);
}

#[test]
fn real_body_mints_one_marker_candidate_per_sentinel() {
    let func = real_resume_body();
    let sinks = func
        .body
        .blocks
        .iter()
        .filter(|block| {
            matches!(&block.terminator, Terminator::Assert { msg, .. }
            if matches!(
                msg,
                AssertMessage::ResumedAfterReturn
                    | AssertMessage::ResumedAfterPanic
                    | AssertMessage::ResumedAfterDrop
            ))
        })
        .count();
    assert_eq!(sinks, 1, "the real zero-await body carries one ResumedAfter* sink");
    assert_eq!(sentinel_markers(&func), vec![(vec![0u128], "resumed after return".to_string())]);
}

#[test]
fn real_body_sentinel_is_proved_unreachable_under_the_exported_precondition() {
    use trust_router::{InProcessAyBackend, VerificationBackend};
    let candidates = sentinel_candidates(&real_resume_body());
    assert_eq!(candidates.len(), 1);
    let backend = InProcessAyBackend::new();
    assert!(backend.can_handle(&candidates[0]), "ay must admit the real candidate");
    // UNSAT = proved on this lane: reaching the sink requires the selector to be
    // the reserved RETURNED=1, which `state in {0}` contradicts.
    assert!(
        matches!(backend.verify(&candidates[0]), trust_types::VerificationResult::Proved { .. }),
        "the real sentinel must be proved unreachable under `state in {{0}}`"
    );
}

#[test]
fn a_wrong_live_set_on_the_real_body_refutes() {
    // NON-VACUITY on production MIR. Routing an extra LIVE (non-reserved) state
    // 3 at the `ResumedAfterReturn` sink makes the exported state set wrong: it
    // claims 3 is resumable while resuming there provably panics with the
    // executor-protocol message. The lane must then REFUTE — the contract fails
    // loudly instead of passing because nobody looked.
    use trust_router::{InProcessAyBackend, VerificationBackend};
    let mut func = real_resume_body();
    let sink = func
        .body
        .blocks
        .iter()
        .find(|block| {
            matches!(&block.terminator, Terminator::Assert { msg, .. }
                if matches!(msg, AssertMessage::ResumedAfterReturn))
        })
        .map(|block| block.id)
        .expect("the real body has a ResumedAfterReturn sink");
    let Terminator::SwitchInt { targets, .. } = &mut func.body.blocks[0].terminator else {
        panic!("the real entry terminator is the resume dispatch SwitchInt")
    };
    targets.push((3, BlockId(sink.0)));

    let markers = sentinel_markers(&func);
    assert_eq!(markers, vec![(vec![0u128, 3], "resumed after return".to_string())]);
    let candidates = sentinel_candidates(&func);
    assert!(
        matches!(
            InProcessAyBackend::new().verify(&candidates[0]),
            trust_types::VerificationResult::Failed { .. }
        ),
        "a wrong live state set must REFUTE the real sentinel"
    );
}
