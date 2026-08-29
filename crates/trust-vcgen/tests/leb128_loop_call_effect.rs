// THE OBLIGATION DELTA ON ay's leb128 LOOP, on REAL EXTRACTED MIR.
//
// `crates/ay-proof-common/proofs/spec_surface/leb128_native_loop.rs` records the
// measured blocker this lane exists to move:
//
//     e45.transition.call-effect -- a CALL anywhere in the loop body leaves the
//         invariant with "no complete exact transition model". This body calls
//         `u32::from` and `data.len()`. Isolated on a minimal fixture: the same
//         loop with no call proves; adding one call turns every clause row into
//         UNKNOWN
//
// The fixture here is the MIR of that exact loop, extracted by the SEALED
// toolchain (`~/toolchains/trust-current`, trust-e26541e3) with
// `-Ztrust-dump=mir-only:<dir>` — the same extractor the probe ran against, and
// one this branch does not touch. The source is `leb128::read_u64` verbatim,
// with only `ParseError`'s definition inlined so the file is self-contained.
//
// WHAT THE REAL MIR SHOWS, and one half of the probe's claim needs correcting:
// the loop contains exactly ONE `Terminator::Call`,
// `<u64 as core::convert::From<u8>>::from(_20)` at bb7, with a by-value `u8`
// argument and a `u64` destination. `data.len()` is NOT a call in the extracted
// body at all — it is already lowered to a length read on the modeled slice, so
// the probe's "this body calls `u32::from` and `data.len()`" over-counts. There
// is one call, and it is the one that blocked the loop.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_vcgen::{bind_compiler_loop_contracts, generate_vcs_with_discharge};

const LEB128_READ_U64: &str = include_str!("fixtures/leb128_read_u64_realmir.json");

/// The natural-loop header of `read_u64`'s `loop { .. }` in the extracted body:
/// bb15 is the latch and branches back here.
const HEADER: usize = 1;

/// The one call in the loop body.
const CALL_BLOCK: usize = 7;

fn leb128() -> VerifiableFunction {
    serde_json::from_str(LEB128_READ_U64).expect("extracted leb128 MIR must deserialize")
}

fn span() -> SourceSpan {
    SourceSpan { file: "leb.rs".to_string(), line_start: 9, col_start: 4, line_end: 9, col_end: 40 }
}

fn invariant_spec(body: &str) -> LoopContractSpec {
    LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 0,
        // Both halves of the compiler-owned identity: `mir_header` alone is
        // refused (`e45.loop-source.unauthenticated-mir-header`), by design.
        source_hir_local_id: Some(1),
        mir_header: Some(HEADER),
        loop_head: SourceSpan { line_end: 26, ..span() },
        header_span: span(),
        span: span(),
        body: body.to_string(),
    }
}

/// Every `UnsupportedMir` detail the loop rows produce, plus which E4 rows exist.
fn outcome(invariant: &str) -> (Vec<String>, bool, bool) {
    let mut func = leb128();
    let failures = bind_compiler_loop_contracts(&mut func, &[invariant_spec(invariant)]);
    assert!(failures.is_empty(), "the loop clause must bind: {failures:?}");
    let (mut vcs, preclassified) = generate_vcs_with_discharge(&func);
    let mut blockers = Vec::new();
    for (vc, _) in &preclassified {
        if let VcKind::UnsupportedMir { kind, detail } = &vc.kind
            && kind == "UserLoopContractUnsupported"
        {
            blockers.push(detail.clone());
        }
    }
    vcs.extend(preclassified.into_iter().map(|(vc, _)| vc));
    let initiation = vcs.iter().any(|vc| matches!(vc.kind, VcKind::LoopInvariantInitiation { .. }));
    let consecution =
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. }));
    (blockers, initiation, consecution)
}

/// The fixture really is the shape the probe describes: one call, in the loop.
#[test]
fn the_extracted_body_has_exactly_one_call_and_it_is_inside_the_loop() {
    let func = leb128();
    let calls = func
        .body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            Terminator::Call { func: callee, args, dest, .. } => {
                Some((block.id.0, callee.clone(), args.len(), dest.local))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        calls,
        vec![(CALL_BLOCK, "<u64 as core::convert::From<u8>>::from".to_string(), 1, 19,)],
        "the extracted body's call set is the measurement's subject",
    );
    // bb15 -> bb1 is the backedge; bb7 is on the path between them.
    assert!(matches!(func.body.blocks[15].terminator, Terminator::Goto(BlockId(HEADER))));
}

/// THE OBLIGATION DELTA, measured.
///
/// BEFORE this lane, every clause on this loop was replaced by one
/// `UnsupportedMir` row reading
/// `e45.transition.call-effect: bb7 … has no complete exact transition model at bb1`.
/// AFTER, that code is gone: the call at bb7 has an exact frame (a by-value
/// `u8` argument, a `u64` scalar destination, `unwind: Continue`, no pointer
/// created anywhere in the body, and the only dereferences in the body are
/// rooted at the modeled `&[u8]`).
///
/// MUTATION-PROVED: with the blanket
/// `Terminator::Call { .. } => Err("e45.transition.call-effect")` arm restored
/// in `symbolic_loop_transitions` and nothing else changed, this test fails
/// with exactly that blocker.
#[test]
fn the_loop_moves_off_call_effect() {
    for invariant in ["shift <= 70", "pos >= start", "1 == 1"] {
        let (blockers, _, _) = outcome(invariant);
        assert!(
            !blockers.iter().any(|detail| detail.contains("e45.transition.call-effect")),
            "`{invariant}`: the leb128 loop must no longer be blocked by the call: {blockers:?}",
        );
    }
}

/// AND WHAT IT DOES NOT BUY, measured rather than assumed. Moving off
/// `call-effect` does not give this loop an E4 row: it is now blocked by
/// `e4.machine.mixed-domain`, because the body mixes a `u32` `shift` with a
/// `u64` `value` and a `usize` `pos` and the machine-faithful translator
/// requires ONE exact declared width.
///
/// That blocker is NOT something this lane introduced. Measured on the SAME
/// body with the call at bb7 replaced by a plain constant assignment and a
/// `Goto` — i.e. the identical loop with no call in it at all — the identical
/// `e4.machine.mixed-domain` row is produced for the identical invariants. The
/// residual refusal is a property of leb128's arithmetic, not of the call.
///
/// So the probe file's ledger for this loop needs a third entry. It named two
/// blockers, `e45.transition.call-effect` and `%`. There are three, and after
/// this lane the binding one is the third.
#[test]
fn the_residual_blocker_is_the_mixed_machine_domain_and_predates_this_lane() {
    let (blockers, initiation, consecution) = outcome("shift <= 70");
    assert!(
        blockers.iter().any(|detail| detail.contains("e4.machine.mixed-domain")),
        "the measured residual blocker: {blockers:?}",
    );
    assert!(!initiation && !consecution, "a refused clause must mint no E4 row");

    // The same loop with the call excised still refuses for the same reason.
    let mut call_free = leb128();
    call_free.body.blocks[CALL_BLOCK].stmts.push(Statement::Assign {
        place: Place::local(19),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
        span: SourceSpan::default(),
    });
    call_free.body.blocks[CALL_BLOCK].terminator = Terminator::Goto(BlockId(8));
    let failures = bind_compiler_loop_contracts(&mut call_free, &[invariant_spec("shift <= 70")]);
    assert!(failures.is_empty(), "{failures:?}");
    let (_, preclassified) = generate_vcs_with_discharge(&call_free);
    let call_free_blockers = preclassified
        .iter()
        .filter_map(|(vc, _)| match &vc.kind {
            VcKind::UnsupportedMir { kind, detail } if kind == "UserLoopContractUnsupported" => {
                Some(detail.clone())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        call_free_blockers.iter().any(|detail| detail.contains("e4.machine.mixed-domain")),
        "the call-free twin must expose the SAME residual blocker, or the claim that this \
         lane did not cause it is wrong: {call_free_blockers:?}",
    );
}

/// The `%` blocker the probe file also names is untouched by this lane, and
/// still refuses for its own reason.
#[test]
fn the_modulus_blocker_is_untouched_and_still_refuses() {
    let (blockers, initiation, consecution) = outcome("shift % 7 == 0");
    assert!(
        blockers.iter().any(|detail| detail.contains("unsupported or ambiguous MIR value")),
        "`%` in a clause predicate must still fail closed, loudly: {blockers:?}",
    );
    assert!(
        !blockers.iter().any(|detail| detail.contains("e45.transition.call-effect")),
        "…and for its OWN reason, not the call: {blockers:?}",
    );
    assert!(!initiation && !consecution, "a refused clause must mint no E4 row");
}
