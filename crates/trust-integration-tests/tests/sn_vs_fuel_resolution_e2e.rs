// trust-integration-tests/tests/sn_vs_fuel_resolution_e2e.rs
//
// THE SN-vs-FUEL RESOLUTION, END-TO-END — the three items of the adopted
// partial-correctness-via-fuel design, driven literally: the VCs consumed by
// trust-certify are exactly the values trust-vcgen returns (no shape
// rebuilding in between).
//
//   ITEM 1 — THREADED BUDGET: the 2-member cluster {ft, gt} over
//     E = A | B(E) | M(E, E) with the (remainder, result) pair
//     Res = Mk(Fuel, E): per-entry decrement (first callee at k), remainder
//     passed to every later callee (`gt(r1.0, y)`), the LAST remainder
//     returned — model-vs-reference against {fr, gr}. Discharged by the
//     MAJORANT `Fuel.rec` induction whose product motive quantifies over ALL
//     threaded fuels (trust-certify's threaded_budget_functional twin
//     documents the shape). NO Acc.
//   ITEM 2 — EXHAUSTION ARMS + DONE-CONDITIONAL POSTS: the PEELER model
//     (fuel Z => Exh(partial); S k + head-normal => Done; S k + wrapper =>
//     tail call) with `forall r, _0 = Done r -> r = A`, plus the machine-built
//     FUEL-MONOTONICITY lane lemma. Negative control: the Exhausted-only
//     postcondition must NOT certify unconditionally (kernel-witnessed).
//   ITEM 3 — LOOP -> FUEL MODEL: the whnf_outer_loop-shaped LOOP fixture
//     (in-program counter decrement + exhausted-bail returning the partial +
//     the back edge) detected and converted to per-iteration SIMULATION VCs,
//     cross-checked arm-by-arm against the model's own induction bundle and
//     discharged definitionally against the SAME rebuilt model — the honest
//     handoff. (The trust-mir-extract loop-model EMISSION path is the named
//     follow-up; the fixtures here are hand-built in the extracted MIR shape,
//     exported by the vcgen lanes' `fixtures` modules.)
//
// Every positive path asserts mint + independent re-check + the load-bearing
// negative witnesses; every negative path is either fail-closed at emission
// or KERNEL-rejected at discharge.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_certify::fuel_outcome_functional::{
    certify_fuel_outcome_functional, certify_loop_fuel_sim, fuel_monotonicity_is_machine_built,
    fuel_outcome_induction_is_load_bearing, recheck_fuel_outcome_functional, recheck_loop_fuel_sim,
};
use trust_certify::threaded_budget_functional::{
    certify_threaded_budget_functional, recheck_threaded_budget_functional,
    threaded_induction_is_load_bearing,
};
use trust_ir::ProofEvidence;
use trust_types::{Formula, VcKind, VerificationCondition};
use trust_vcgen::fuel_outcome_functional::fixtures as outcome_fixtures;
use trust_vcgen::fuel_outcome_functional::{fuel_outcome_functional_vcs, loop_fuel_sim_vcs};
use trust_vcgen::threaded_budget_functional::fixtures as threaded_fixtures;
use trust_vcgen::threaded_budget_functional::threaded_budget_functional_vcs;

fn property(vc: &VerificationCondition) -> &str {
    match &vc.kind {
        VcKind::FunctionalCorrectness { property, .. } => property,
        other => panic!("expected FunctionalCorrectness, got {other:?}"),
    }
}

// ── Item 1: the threaded-budget cluster, end-to-end ──────────────────────────

#[test]
fn threaded_budget_cluster_certifies_end_to_end() {
    let funcs = threaded_fixtures::threaded_cluster();
    let vcs = threaded_budget_functional_vcs(&funcs);
    assert_eq!(vcs.len(), 17, "2 bases + 6 cases + 2 refbases + 6 refcases + conclusion");
    assert!(
        property(&vcs[16]).contains("threaded-induction:fuel=fuel::Fuel:Z|S;res=res::Res:Mk"),
        "the conclusion is marker-bound: {}",
        property(&vcs[16])
    );

    // The literal emitted bundle discharges.
    let evidence = certify_threaded_budget_functional(&vcs)
        .expect("the threaded model=reference bundle must certify");
    let ProofEvidence::CleanCic { term, context, lineage, .. } = &evidence else {
        panic!("expected CleanCic evidence, got {evidence:?}");
    };
    assert!(
        recheck_threaded_budget_functional(&vcs, term, context, lineage),
        "the serialized certificate must independently re-check"
    );

    // The majorant induction is load-bearing: the refl-only pseudo-proof is
    // kernel-REJECTED against the same goal.
    assert!(threaded_induction_is_load_bearing(&vcs));

    // Tamper negative: one flipped byte in the term fails the re-check.
    let mut tampered = term.clone();
    *tampered.last_mut().expect("nonempty term") ^= 0x5a;
    assert!(!recheck_threaded_budget_functional(&vcs, &tampered, context, lineage));
}

#[test]
fn threaded_non_threaded_model_fails_closed_at_emission() {
    // The M arm's second call re-spends `k` instead of consuming the first
    // call's remainder: not a threaded bundle — no VCs at all.
    let funcs = vec![
        threaded_fixtures::threaded_fn("ft", "gt", vec![threaded_fixtures::ref_post("fr")], false),
        threaded_fixtures::threaded_fn("gt", "ft", vec![threaded_fixtures::ref_post("gr")], true),
        threaded_fixtures::threaded_fn("fr", "gr", vec![], true),
        threaded_fixtures::threaded_fn("gr", "fr", vec![], true),
    ];
    assert!(threaded_budget_functional_vcs(&funcs).is_empty());
}

#[test]
fn threaded_disagreeing_reference_is_kernel_rejected() {
    // Flip ONE emitted reference VC into a parseable-but-false arm: gr's B
    // step becomes CALL-FREE, returning the un-spent budget `Mk(k, B x)` —
    // pointwise unequal to the threaded model. The bundle still parses; the
    // KERNEL rejects the joint proof.
    let funcs = threaded_fixtures::threaded_cluster();
    let mut vcs = threaded_budget_functional_vcs(&funcs);
    let idx = vcs
        .iter()
        .position(|vc| property(vc) == "threaded_budget_functional_refstep::gr::B[calls=fr]")
        .expect("gr's B refstep is in the bundle");
    let fuel_sort = threaded_fixtures::fuel_sort();
    let e_sort = threaded_fixtures::e_sort();
    let res_sort = threaded_fixtures::res_sort();
    let k = Formula::var_owned("__fld_S_0".to_string(), fuel_sort.clone());
    let x = Formula::var_owned("__fld_B_0".to_string(), e_sort.clone());
    let s_k = Formula::Ctor { ctor: "S".to_string(), args: vec![k.clone()], sort: fuel_sort };
    let b_x = Formula::Ctor { ctor: "B".to_string(), args: vec![x], sort: e_sort.clone() };
    let call_free = Formula::forall(
        &[
            ("__fld_S_0", threaded_fixtures::fuel_sort()),
            ("__fld_B_0", threaded_fixtures::e_sort()),
        ],
        Formula::Eq(
            Box::new(Formula::FnApp {
                func: "gr".to_string(),
                args: vec![s_k, b_x.clone()],
                sort: res_sort.clone(),
            }),
            Box::new(Formula::Ctor { ctor: "Mk".to_string(), args: vec![k, b_x], sort: res_sort }),
        ),
    );
    vcs[idx].formula = call_free;
    vcs[idx].kind = VcKind::FunctionalCorrectness {
        property: "threaded_budget_functional_refstep::gr::B[calls=]".to_string(),
        context: "gr".to_string(),
    };
    assert!(
        certify_threaded_budget_functional(&vcs).is_none(),
        "a reference arm that skips the call is pointwise unequal — no certificate"
    );
}

// ── Item 2: exhaustion arms + Done-conditional posts, end-to-end ─────────────

#[test]
fn fuel_outcome_peeler_certifies_end_to_end() {
    let model = outcome_fixtures::peel_model_fn(
        "peel_model",
        vec![outcome_fixtures::done_conditional_post()],
    );
    let vcs = fuel_outcome_functional_vcs(&model);
    assert_eq!(vcs.len(), 4, "base + A case + B tail case + conclusion");
    assert!(property(&vcs[0]).starts_with("fuel_outcome_functional_base::"));

    let evidence = certify_fuel_outcome_functional(&vcs)
        .expect("the Done-conditional peeler bundle must certify");
    let ProofEvidence::CleanCic { term, context, lineage, .. } = &evidence else {
        panic!("expected CleanCic evidence, got {evidence:?}");
    };
    assert!(recheck_fuel_outcome_functional(&vcs, term, context, lineage));
    assert!(fuel_outcome_induction_is_load_bearing(&vcs));

    // The item-2 LANE LEMMA: fuel-monotonicity is machine-built and
    // kernel-checked for this model (and the downward variant rejected).
    assert!(fuel_monotonicity_is_machine_built(&vcs));
}

#[test]
fn exhausted_only_postcondition_is_kernel_rejected() {
    // `_0 = Exh(A)` holds ONLY on the exhaustion arm; the complete arm's
    // `Done(A)` refutes it inside the kernel. Emission is spec-driven (the
    // bundle exists); certification must fail.
    let model = outcome_fixtures::peel_model_fn(
        "peel_model",
        vec![outcome_fixtures::exhausted_only_post()],
    );
    let vcs = fuel_outcome_functional_vcs(&model);
    assert_eq!(vcs.len(), 4, "emission is spec-driven");
    assert!(
        certify_fuel_outcome_functional(&vcs).is_none(),
        "a postcondition that holds only on the Exhausted arm must NOT certify"
    );
}

#[test]
fn false_done_conditional_is_kernel_rejected() {
    let model =
        outcome_fixtures::peel_model_fn("peel_model", vec![outcome_fixtures::wrong_done_post()]);
    let vcs = fuel_outcome_functional_vcs(&model);
    assert_eq!(vcs.len(), 4, "emission is spec-driven");
    assert!(certify_fuel_outcome_functional(&vcs).is_none());
}

// ── Item 3: the loop -> fuel-model simulation, end-to-end ────────────────────

#[test]
fn loop_fuel_sim_certifies_end_to_end() {
    let model = outcome_fixtures::peel_model_fn(
        "peel_model",
        vec![outcome_fixtures::done_conditional_post()],
    );
    let lp = outcome_fixtures::peel_loop_fn("peel_loop", true);
    let sim = loop_fuel_sim_vcs(&lp, &model);
    assert_eq!(sim.len(), 4, "bail + done A + continue B + conclusion");
    assert_eq!(property(&sim[0]), "loop_fuel_sim_bail::peel_loop");
    assert_eq!(property(&sim[2]), "loop_fuel_sim_continue::peel_loop::B");

    // The handoff: the sim equations discharge against the SAME model the
    // induction bundle rebuilds (cross-checked arm-by-arm inside).
    let bundle = fuel_outcome_functional_vcs(&model);
    let evidence = certify_loop_fuel_sim(&sim, &bundle)
        .expect("every loop path is one iota step of the fuel model");
    let ProofEvidence::CleanCic { term, context, lineage, .. } = &evidence else {
        panic!("expected CleanCic evidence, got {evidence:?}");
    };
    assert!(recheck_loop_fuel_sim(&sim, &bundle, term, context, lineage));

    // And the model's own induction bundle certifies (item 2) — together the
    // chain loop -> model -> Done-conditional theorem is fully kernel-checked.
    assert!(certify_fuel_outcome_functional(&bundle).is_some());
}

#[test]
fn loop_without_decrement_fails_closed() {
    let model = outcome_fixtures::peel_model_fn(
        "peel_model",
        vec![outcome_fixtures::done_conditional_post()],
    );
    let lp = outcome_fixtures::peel_loop_fn("peel_loop", false);
    assert!(
        loop_fuel_sim_vcs(&lp, &model).is_empty(),
        "a loop that never decrements its counter does not simulate a fuel model"
    );
}
