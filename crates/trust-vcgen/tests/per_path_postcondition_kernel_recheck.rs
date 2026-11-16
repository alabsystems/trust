//! THE a7 PER-PATH POSTCONDITION ROW IS KERNEL-CERTIFIABLE — RULING C closed.
//!
//! # What RULING C said, and what was actually true
//!
//! The a7 lane (`docs/STRICT_VERIFICATION_FRAGMENT.md` §19.3,
//! `fix(vcgen): one postcondition row per enumerated return path`) made a
//! `Return`-block predecessor reached by `n` guard paths emit `n` FLAT rows
//! instead of one `Or` of `n`. It closed the conditional-postcondition blocker
//! and cost `tests/ui/trust/postcondition_composition_at_call_site.rs`'s
//! `clamp_low` its one kernel-certified row, recorded as RULING C:
//!
//! > Every flat per-path row is proved by trust-mc PDR directly, which answers
//! > first, so the kernel re-check never runs.
//!
//! **That mechanism is false, and this file is the measurement that refutes it.**
//! `certify_all` in `trust_verify.rs` runs `trust_certify::certify_vc` on EVERY
//! `Proved` row, whatever engine proved it, and `ResultProofAuthority::
//! KernelCertified` is minted from nothing but that call's result. Measured on
//! the packed `trustc 1.99.0-dev (379912412 2026-09-19)` with
//! `TRUST_CERTIFY_TRACE=1`, all three of `clamp_low`'s split rows ENTER the
//! producer and MISS it. The re-check ran; it simply could not reach the shape.
//!
//! And it could not reach the shape before the split either. At
//! `POSTCONDITION_PATH_SPLIT_CAP = 1` the flat `x < 0` row is uncertified too —
//! only the merged `Or` row certified, because
//! `certify_disjunctive_contradiction` (the one lane that can distribute the
//! negated range conjunction `Not(And([Ge(_0,0), Le(_0,1000000)]))`) returns
//! `None` at its `or_candidates.is_empty()` gate on a disjunction-free pool. The
//! split did not break a working lane: it replaced the one shape this producer
//! could reach with three of a shape it could not.
//!
//! The fix is `trust_certify::certify_singleton_disjunction_retry` — a
//! last-resort rung that re-presents a flat violation to that same engine as a
//! ONE-ARM disjunction. `Or([F])` is `F`, and `build_or_prop` emits a
//! one-element list as the arm's own proposition, so the kernel term carries no
//! wrapper. Nothing about the engine, its caps, or its ay-UNSAT-plus-kernel
//! backstop changes.
//!
//! # What these tests measure, and what they do NOT claim
//!
//! They call the real producer on real extracted MIR
//! (`-Ztrust-dump=mir:<dir>`, packed toolchain) and assert `certify_vc`'s
//! Boolean. `certify_vc` returning `Some` is EXACTLY the condition
//! `build_proof_results` mints `KernelCertified` on, so these tests bound the
//! "of which N kernel-certified" note — but the note itself is emitted by the
//! compiler, and confirming its text needs a stage build. That measurement is
//! the integrator's; it is named in this lane's handoff, not asserted here.

use trust_types::*;
use trust_vcgen::generate_vcs;

/// The postcondition rows of a fixture, in emission order. For all three
/// fixtures below that is one row per enumerated return path:
/// `0` = `x < 0`, `1` = the inner join (`0 <= x <= 1000000`), `2` = `x > 1000000`.
fn postcondition_rows(src: &str) -> Vec<VerificationCondition> {
    let func: VerifiableFunction = serde_json::from_str(src).expect("fixture MIR must deserialize");
    generate_vcs(&func).into_iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect()
}

fn certified(rows: &[VerificationCondition]) -> Vec<bool> {
    rows.iter().map(|vc| trust_certify::certify_vc(vc).is_some()).collect()
}

/// POSITIVE. `clamp_low` — the exact body and clause of
/// `tests/ui/trust/postcondition_composition_at_call_site.rs`, whose lost
/// kernel-certified row RULING C records.
///
/// Measured on the packed toolchain: `[false, false, false]` at HEAD,
/// `[true, true, true]` with the retry rung. Three is MORE than the one
/// certified row the merged `Or` shape carried before the split, so the a7
/// capability is kept and the cost RULING C priced is repaid with interest.
#[test]
fn every_per_path_row_of_a_true_clause_is_kernel_certified() {
    let rows = postcondition_rows(include_str!("fixtures/per_path_postcondition_clamp_low.json"));
    assert_eq!(rows.len(), 3, "the three-arm chain must emit one row per enumerated path");
    assert_eq!(
        certified(&rows),
        vec![true, true, true],
        "each per-path row of a TRUE clause must be re-checked by the clean CIC kernel; \
         at HEAD all three read `false` and the function's report carried no \
         `of which N kernel-certified` note",
    );
}

/// CLOSE NEGATIVE TWIN. The same body with the `x < 0` arm returning `2000000`,
/// which violates `result <= 1000000`. Only that arm changes.
///
/// The row that must NOT certify is the one whose own path is violated, and its
/// two TRUE siblings must still certify — the same path-isolation property
/// §19.3 called the strongest evidence the split is sound, now measured one
/// level down at the kernel. A lane that certified row 0 here would be minting a
/// kernel certificate for a false postcondition: the cardinal sin.
#[test]
fn the_violating_per_path_row_is_not_certified_and_its_siblings_still_are() {
    let rows = postcondition_rows(include_str!(
        "fixtures/per_path_postcondition_clamp_low_false_one_path.json"
    ));
    assert_eq!(rows.len(), 3, "the false twin must emit the same three per-path rows");
    assert_eq!(
        certified(&rows),
        vec![false, true, true],
        "exactly the violated path (`x < 0` returning 2000000) must stay uncertified",
    );
}

/// MUTATION CONTROL, and it moves the OTHER operand. The body is the true
/// `clamp_low`; the CLAUSE bound is tightened to `result <= 999999`. That makes
/// the `x > 1000000` arm (returns `1000000`) and the join arm (`x` may be
/// `1000000`) false while leaving the `x < 0` arm (returns `0`) true.
///
/// So the certified set INVERTS relative to the negative twin above. A lane
/// keyed on the body shape, on the row index, or on "this family always
/// certifies" passes one of these two tests and fails the other; only a lane
/// that actually refutes THIS row's formula passes both.
#[test]
fn tightening_the_clause_bound_inverts_exactly_which_rows_certify() {
    let rows = postcondition_rows(include_str!(
        "fixtures/per_path_postcondition_clamp_low_tight_bound.json"
    ));
    assert_eq!(rows.len(), 3, "the control must emit the same three per-path rows");
    assert_eq!(
        certified(&rows),
        vec![true, false, false],
        "only the `x < 0` arm satisfies `result <= 999999`; the other two must fail closed",
    );
}
