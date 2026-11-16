//! REAL-ARTIFACT instrument for the full-assert REFUTATION lane's grounding of a
//! PLACE COMPONENT of a function input.
//!
//! # What this pins
//!
//! `generate_full_assert_refutation_vcs` is the lane that turns a user
//! `assert!`/`panic!` into a path-feasibility formula ay decides in BOTH
//! directions: SAT is a counterexample (the falsification gate's REFUTED
//! verdict), UNSAT is an all-inputs proof. The lane emits a candidate only when
//! every free variable of the formula is an unconstrained function input or is
//! PINNED by an exact definition (`grounded`); otherwise it declines, because a
//! SAT model over an unpinned variable need not describe an executable path.
//!
//! Two deliberate 2026-08-28 tightenings narrowed what counts as grounded:
//!
//!   * `3d1446f4c7` ("ground constrained assert inputs") removed the
//!     single-assignment leaf-read admission from `v2_input_free_locals`. A copy,
//!     a constant, a `Discriminant` read, or a payload extraction of an input is
//!     no longer *independently* free — its relationship to the source value
//!     "must be grounded by an exact definition". That closed a real FALSE
//!     REFUTATION class (a formula naming both sides could pick inconsistent
//!     values).
//!   * `e6fae3f5be` ("require exact refutation path guards") added
//!     `guard_to_refutation_formula`, which keeps a Boolean switch discriminant
//!     as its RAW value instead of using the proof-facing one-way summaries, and
//!     says so in its own doc: *"the refutation producer must subsequently pin
//!     that value to an exact definition or decline."*
//!
//! Both are right, and neither is relaxed. The coverage they requisitioned was
//! missing and is now supplied, as the two EXACT PINS named in
//! `reports/falsification/2026-09-10-gate-RED-290-25-root-cause.md` §C:
//!
//!   1. a `@variant.field` projection of an entry-stable parameter is a COMPONENT
//!      of that unconstrained input, so it is free — GUARDED by
//!      `refutation_names_may_alias`, which declines the whole candidate whenever
//!      two names in the emitted conjunction may denote overlapping storage (a
//!      whole and its part, two downcasts of one enum, two symbolic indices of one
//!      array). That guard is what keeps `3d1446f4c7`'s channel closed; a bare
//!      base-name exemption, which would re-open it, was explicitly NOT taken.
//!   2. `dest == __trust_mir__discr_<src>` for a `Discriminant` read of an
//!      input-free place, with the enum's own inhabited-variant membership riding
//!      along so the tag cannot take a phantom value no variant carries.
//!
//! # The fixtures are the compiler's own extracted verification input
//!
//! Captured verbatim with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib --emit=metadata -Cpanic=abort \
//!        -Ztrust-dump=mir-only:<dir> -Ztrust-policy=advisory <source>
//! ```
//!
//! from trustc `8b50cbcc5b` (2026-09-10), so they are not hand-built
//! approximations of the MIR — they are the MIR. Two come from the falsification
//! corpus (`tests/trust-falsification/{mutant,proved}/…`); the SAFE twin's source
//! sits beside its JSON in `tests/data/` (it is a vcgen property, not a
//! compiler-gate fixture, so it deliberately does not enlarge that corpus).
//!
//! # Three directions, all load-bearing
//!
//!   * the MUTANT must REFUTE with a witness — the falsification gate reads
//!     anything less as an uncaught mutant;
//!   * its SAFE twin must GROUND and come out UNSAT — a model there would be a
//!     FALSE REFUTATION of correct Rust, which is strictly worse than the missing
//!     refutation this lane restores;
//!   * `proved/foreach_range_safe.rs` must still DECLINE, and the reason is
//!     recorded rather than papered over: its blocker is a DIFFERENT gap.

use trust_types::{VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");

/// STRAIGHT FROM TEXT, never through `serde_json::Value`: that type's number
/// representation silently widens a 128-bit constant to `f64` on the hop.
fn load(name: &str) -> VerifiableFunction {
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("assert-refutation MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("assert-refutation MIR fixture `{name}` must deserialize: {e}"))
}

/// The per-path verdicts the compiler's `refute_full_assert_obligations` would
/// read, decided by the real in-process ay.
fn ay_verdicts(vcs: &[trust_types::VerificationCondition]) -> Vec<VerificationResult> {
    let router = test_router::deterministic_test_router();
    vcs.iter()
        .map(|vc| {
            let results = router.verify_all(std::slice::from_ref(vc));
            let (_, result) = results.into_iter().next().expect("one verdict per VC");
            result
        })
        .collect()
}

/// The extracted MIR really does carry the shapes this lane is about. Asserted
/// explicitly so a re-dump that loses them fails loudly here instead of making
/// the measurements below silently weaker.
#[test]
fn the_real_mir_carries_the_user_assert_panic_call() {
    for name in [
        "assert_refutation_gap_match_nested_tuple",
        "assert_refutation_gap_match_nested_tuple_safe",
        "assert_refutation_gap_foreach_range_safe",
    ] {
        let func = load(name);
        let has_panic_call = func.body.blocks.iter().any(|block| {
            matches!(
                &block.terminator,
                trust_types::Terminator::Call { func, .. } if func.contains("panic")
            )
        });
        assert!(has_panic_call, "`{name}` must still carry a user assert's panic call");
    }
}

/// `mutant/match_nested_tuple.rs` — `match o { Some((a, b)) => assert!(a == b) }`.
///
/// MEASURED on the MIR trustc `8b50cbcc5b` extracted (2026-09-10), before the two
/// pins: the refutation formula was `_2#s0_0 == 1 AND NOT(_5#s3_2)` with
/// `grounded=false`, `candidates=0`, because
///
///   * `_5#s3_2` (the raw Boolean switch discriminant `e6fae3f5be` keeps) resolves
///     only through `a#s3_0 == o@1.0.0` / `b#s3_1 == o@1.0.1`, and `o@1.0.0` — the
///     enum-payload projection of the input-free parameter `o` — was not
///     recognised as free: `is_free` stripped only the `#sN_M` version token and
///     `def_base_name` only a trailing numeric `.k`, neither of which reaches an
///     `@variant.field` spelling; and
///   * `_2#s0_0`, the `Discriminant(o)` read, had no candidate definition at all.
///
/// With both pins the formula grounds, splits into its two control-flow paths, and
/// the `Some` path is SAT with a witness that names a real argument — the verdict
/// trustc `acb08e7616` (2026-08-21, before both tightenings) produced.
#[test]
fn nested_tuple_payload_assert_grounds_and_refutes_with_a_witness() {
    let func = load("assert_refutation_gap_match_nested_tuple");
    let vcs = trust_vcgen::generate_full_assert_refutation_vcs(&func);
    // One obligation per control-flow path to the panic block: the `None` arm
    // (`discr == 0`, which cannot reach it) and the `Some` arm (`discr == 1`).
    assert_eq!(vcs.len(), 2, "one obligation per path to the failure block; got {}", vcs.len());

    // The pins must be PRESENT, not merely implied by the count: the payload
    // projections and the discriminant carrier are the two artifacts of this lane.
    let vocabulary: Vec<String> = vcs.iter().flat_map(|vc| vc.formula.free_variables()).collect();
    for expected in ["o@1.0.0", "o@1.0.1", "__trust_mir__discr_o"] {
        assert!(
            vocabulary.iter().any(|v| v == expected),
            "the grounded formula must name `{expected}`; vocabulary: {vocabulary:?}"
        );
    }

    let verdicts = ay_verdicts(&vcs);
    let refuted: Vec<&VerificationResult> = verdicts
        .iter()
        .filter(|result| matches!(result, VerificationResult::Failed { .. }))
        .collect();
    assert_eq!(
        refuted.len(),
        1,
        "exactly the `Some` path is feasible, so exactly one part must refute; got {verdicts:?}"
    );
    // A refutation without a witness is not a counterexample. The model must name
    // a real argument — two DIFFERENT payload fields under the `Some` tag.
    let VerificationResult::Failed { counterexample: Some(counterexample), .. } = refuted[0] else {
        panic!("the refuted path must carry a counterexample; got {:?}", refuted[0]);
    };
    let assignment = |name: &str| {
        counterexample
            .assignments
            .iter()
            .find(|(var, _)| var == name)
            .map(|(_, value)| value.clone())
    };
    assert_eq!(
        assignment("__trust_mir__discr_o"),
        Some(trust_types::CounterexampleValue::Int(1)),
        "the witness must take the `Some` arm; model: {:?}",
        counterexample.assignments
    );
    let (Some(first), Some(second)) = (assignment("o@1.0.0"), assignment("o@1.0.1")) else {
        panic!("the witness must bind both payload fields; model: {:?}", counterexample.assignments)
    };
    assert_ne!(
        first, second,
        "the witness must violate `a == b`; model: {:?}",
        counterexample.assignments
    );
}

/// The FALSE-REFUTATION direction, on the SAFE twin of the fixture above
/// (`tests/data/assert_refutation_gap_match_nested_tuple_safe.rs` —
/// `assert!(a == a); assert!(b == b);`, both true for every input).
///
/// The same two pins ground it, and every path must come out UNSAT. A model here
/// would accuse correct Rust, which is exactly the failure `3d1446f4c7` closed and
/// which the overlapping-place guard exists to keep closed.
///
/// Four obligations: two panic blocks (one per assert), each split into its
/// `None` and `Some` control-flow path.
#[test]
fn safe_nested_tuple_payload_assert_grounds_and_proves() {
    let func = load("assert_refutation_gap_match_nested_tuple_safe");
    let vcs = trust_vcgen::generate_full_assert_refutation_vcs(&func);
    assert_eq!(vcs.len(), 4, "two asserts x two paths to their failure blocks; got {}", vcs.len());
    // Both sibling payload projections must appear: their DISJOINTNESS is the
    // claim `refutation_names_may_alias` makes, and a fixture that only ever named
    // one of them would not exercise it.
    let vocabulary: Vec<String> = vcs.iter().flat_map(|vc| vc.formula.free_variables()).collect();
    for expected in ["o@1.0.0", "o@1.0.1", "__trust_mir__discr_o"] {
        assert!(
            vocabulary.iter().any(|v| v == expected),
            "the grounded formulas must name `{expected}`; vocabulary: {vocabulary:?}"
        );
    }
    for (index, result) in ay_verdicts(&vcs).into_iter().enumerate() {
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "path {index}: an always-true payload assert must be UNSAT (Proved = the panic \
             path is unreachable); got {result:?}\nformula: {:?}",
            vcs[index].formula
        );
    }
    // An ay `Proved` the clean kernel does not certify is reported `Unknown` under
    // `-Ztrust-policy=certify`, so the proving direction is only worth as much as
    // its certificate.
    for (index, vc) in vcs.iter().enumerate() {
        assert!(
            trust_certify::certify_vc(vc).is_some(),
            "path {index}: the proved panic path must kernel-certify; formula: {:?}",
            vc.formula
        );
    }
}

/// `proved/foreach_range_safe.rs` — `for _ in 0..n { assert!(x == x); }`.
///
/// STILL DECLINES, and this assertion records WHY rather than treating the two
/// pins as covering it. MEASURED on this fixture with both pins in place:
///
///   [ASSERT_REFUTE] block=BlockId(7) grounded=false free=["_8#s3_0", "_9#s5_0"]
///   [ASSERT_CAND]   resolved=[…, "_9#s5_0"]
///
/// `_9#s5_0` (the `x == x` comparison) DOES resolve — it always did, and the
/// earlier note here that neither free variable had a pin was wrong. The sole
/// blocker is `_8#s3_0`, the `Discriminant` read of `_6`, and `_6` is the
/// destination of `<Range<usize> as Iterator>::next` — an OPAQUE CALL RESULT, not
/// an input-free place. `discriminant_pin_defs` therefore declines it, and that is
/// correct: freeing the tag of a value a callee chose would let a SAT model pick a
/// return the callee never produces, which is a false refutation. Closing it needs
/// an exact model of `Range::next`, a different and larger piece of work than the
/// two pins above; until then this fixture's whole-function panic-freedom row
/// stays runtime-checked.
///
/// If this count is ever 1, that model landed — flip the expectation and
/// re-measure `scripts/trust_falsification_gate.sh`.
#[test]
fn foreach_range_true_assert_still_declines_on_an_opaque_iterator_discriminant() {
    let func = load("assert_refutation_gap_foreach_range_safe");
    let vcs = trust_vcgen::generate_full_assert_refutation_vcs(&func);
    assert_eq!(
        vcs.len(),
        0,
        "OPEN GAP (see this test's doc): the loop's `Option` tag comes from an opaque \
         `Iterator::next` call, which the exact discriminant pin correctly refuses."
    );
}
