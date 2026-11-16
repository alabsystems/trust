//! REAL-ARTIFACT regression guard for the BMC bounded-reduction REFUTATION lane.
//!
//! The two fixtures under `tests/data/` are the compiler's OWN extracted
//! verification input, captured verbatim from the repository root with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib --emit=metadata -Cpanic=abort \
//!        -Ztrust-dump=mir:<dir> crates/trust-vcgen/tests/data/bmc_reduction_arms.rs
//! ```
//!
//! so they are not hand-built approximations of the MIR — they are the MIR, and
//! `bmc_reduction_arms.rs` is committed beside them so every row can be
//! re-derived.
//!
//! # Why this file exists
//!
//! `generate_bounded_reduction_bmc_refutation_candidates` is exercised by 40-odd
//! unit tests over hand-built `VerifiableFunction`s in
//! `src/generate/bmc_reduction/tests.rs`. Those tests have now been green across
//! TWO separate regressions in which the lane did not fire on the real extracted
//! MIR at all:
//!
//!   * `086b157aca` (2026-08-14) landed the lane with 20 passing unit tests and
//!     it never fired end to end, because the real MIR carries an always-true
//!     `Option`-tag precondition and a `SwitchInt` whose `otherwise` edge points
//!     at an `Unreachable`. `d8059bf397` closed both holes.
//!   * `4ca0cb0eac` (2026-08-21) removed the `otherwise`-edge argument again
//!     (`crates/trust-vcgen/src/generate/bmc_reduction.rs`, `bmc_terminator_succs`).
//!     Every synthetic test stayed green — the default synthetic fixture spells
//!     the switch as `1 -> body, otherwise -> return` with no `Unreachable`
//!     anywhere — while `tests/trust-falsification/mutant/shift_reduction_overflow.rs`
//!     silently went from `refuted` back to `incomplete` on the falsification
//!     gate.
//!
//! The fixture's own header states the rule this file enforces: *"Unit tests over
//! synthetic shapes are not evidence that a recognizer fires on real MIR."*

use trust_types::{BinOp, VcKind, VerifiableFunction};

#[path = "support/test_router.rs"]
mod test_router;

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");

/// STRAIGHT FROM TEXT, never through `serde_json::Value`: that type's number
/// representation silently widens a 128-bit constant to `f64` on the hop.
fn load(name: &str) -> VerifiableFunction {
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("BMC MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("BMC MIR fixture `{name}` must deserialize: {e}"))
}

/// The extracted MIR really does carry the two shapes this lane has twice
/// tripped over. Asserted explicitly so a future re-dump that loses them turns
/// into a loud failure here rather than a silently weaker test below.
#[test]
fn the_real_mir_carries_the_option_tag_switch_and_its_unreachable_arm() {
    let func = load("bmc_shift_reduction_overflow");
    let switch = func
        .body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            trust_types::Terminator::SwitchInt { targets, otherwise, .. } => {
                Some((targets.clone(), *otherwise))
            }
            _ => None,
        })
        .expect("the for-each desugar must emit exactly one SwitchInt");
    let (targets, otherwise) = switch;
    let mut cases: Vec<u128> = targets.iter().map(|(v, _)| *v).collect();
    cases.sort_unstable();
    assert_eq!(cases, vec![0, 1], "the case set is the Option tag set");
    assert!(
        func.body
            .blocks
            .iter()
            .any(|b| b.id == otherwise
                && matches!(b.terminator, trust_types::Terminator::Unreachable)),
        "rustc closes the Option switch with `otherwise -> Unreachable`; that edge is \
         what `bmc_terminator_succs` must argue dead from the scrutinee's DECLARED enum type"
    );
    assert!(
        !func.preconditions.is_empty(),
        "the extractor mints the always-true `_7 = 0 or _7 = 1` tag hypothesis; \
         `preconditions_leave_the_input_free` must certify it as a type tautology"
    );
}

/// The load-bearing one: the mutant that the falsification gate scores.
#[test]
fn the_shift_reduction_mutant_yields_a_candidate_on_real_mir() {
    let func = load("bmc_shift_reduction_overflow");
    assert!(
        trust_vcgen::validate_function(&func).is_ok(),
        "the real extracted MIR must be well-formed TrustIR, so a refusal below is \
         the BMC lane's own decision and not a structural rejection"
    );
    let candidates = trust_vcgen::generate_bounded_reduction_bmc_refutation_candidates(&func);
    assert_eq!(
        candidates.len(),
        1,
        "the BMC bounded-reduction lane must fire on the REAL extracted MIR of \
         tests/trust-falsification/mutant/shift_reduction_overflow.rs — this is the \
         gate row that regressed at 4ca0cb0eac"
    );
    assert!(
        matches!(&candidates[0].kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }),
        "the refuted obligation must carry the REAL L0 kind, got {:?}",
        candidates[0].kind
    );
    assert_eq!(
        candidates[0].location.line_start, 11,
        "the row must point at the `t += ...` statement in bmc_reduction_arms.rs"
    );
}

/// The producer is shape-driven, not outcome-driven, so the SAFE twin also gets
/// a candidate. Soundness rests on the consumer dropping UNSAT — which the next
/// test measures against the real solver.
#[test]
fn the_safe_twin_also_yields_a_candidate_on_real_mir() {
    let func = load("bmc_safe_widening_reduction");
    assert_eq!(trust_vcgen::generate_bounded_reduction_bmc_refutation_candidates(&func).len(), 1);
}

/// End to end through the SAME router the compiler's consumer uses
/// (`refute_bounded_reduction_bmc_overflows` in
/// `compiler/rustc_mir_transform/src/trust_verify.rs`): the overflowing mutant is
/// SAT with a NON-EMPTY model (which is the only thing that licenses a `Failed`
/// row), and the safe twin is NOT.
///
/// "The same router" includes its clock. The consumer builds
/// `deterministic_in_process_ay(timeout_ms, effort_scale(sess))` with `timeout_ms`
/// at most `vc_timeout_ms(sess)`, which `targo trust` sets to
/// `Backstop::BUILTIN.vc_clock_ms()` (5,000 ms), so this test solves at that clock
/// ([`test_router::shipped_vc_clock_router`]). A refutation that needs more than
/// the shipped clock is lost on the falsification gate (the row reads `incomplete`
/// again, the regression this file exists for), and this test fails with it rather
/// than passing on a longer clock (VCGEN-TEST-BACKSTOP-1, kept sites). It is the
/// only solving test in this binary, so no other test of the binary queues on ay's
/// execution lock in front of it.
#[test]
fn ay_refutes_the_mutant_with_a_witness_and_never_the_safe_twin() {
    let router = test_router::shipped_vc_clock_router();

    let mutant = load("bmc_shift_reduction_overflow");
    let candidates = trust_vcgen::generate_bounded_reduction_bmc_refutation_candidates(&mutant);
    assert_eq!(candidates.len(), 1);
    let (_, res) = router
        .verify_all(&candidates)
        .into_iter()
        .next()
        .expect("the router must answer the candidate");
    match res {
        trust_types::VerificationResult::Failed { counterexample: Some(cex), .. } => {
            assert!(
                !cex.assignments.is_empty(),
                "a witness-less Failed is DROPPED by the consumer, so it would not \
                 restore the gate row"
            );
            // The witness must be a REAL input, not just a non-empty map: all 64
            // elements assigned, each inside `u8`, and a final accumulator past
            // `u8::MAX`. (The model ay actually returns here is the one the
            // fixture header records by hand — elem62 = 1, elem63 = 15, so
            // t = 16 then 16 + (15 << 4) = 256 — but pinning one corner would be
            // brittle, so this pins the PROPERTY that makes any corner genuine.)
            let value_of = |name: &str| {
                cex.assignments.iter().find(|(k, _)| k == name).map(|(_, v)| v.clone())
            };
            for i in 0..64 {
                match value_of(&format!("__trust_bmc_elem{i}")) {
                    Some(trust_types::CounterexampleValue::Int(v)) => assert!(
                        (0..=255).contains(&v),
                        "element {i} = {v} is outside u8; a witness must be a real input"
                    ),
                    other => panic!("element {i} must carry an integer witness, got {other:?}"),
                }
            }
            match value_of("__trust_bmc_acc64") {
                Some(trust_types::CounterexampleValue::Int(v)) => assert!(
                    v > 255,
                    "the witnessed running sum must actually exceed u8::MAX, got {v}"
                ),
                other => panic!("the final accumulator must be witnessed, got {other:?}"),
            }
        }
        other => {
            panic!("the genuinely-overflowing reduction must be SAT with a model; got {other:?}")
        }
    }

    let safe = load("bmc_safe_widening_reduction");
    let safe_candidates = trust_vcgen::generate_bounded_reduction_bmc_refutation_candidates(&safe);
    assert_eq!(safe_candidates.len(), 1);
    let (_, safe_res) = router
        .verify_all(&safe_candidates)
        .into_iter()
        .next()
        .expect("the router must answer the safe candidate");
    assert!(
        !matches!(safe_res, trust_types::VerificationResult::Failed { .. }),
        "`16 * (255 << 4) = 65280` fits u16 — refuting it would be a build error on \
         correct code; got {safe_res:?}"
    );
}
