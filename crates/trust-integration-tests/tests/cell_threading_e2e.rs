// trust-integration-tests/tests/cell_threading_e2e.rs
//
// TEST-ONLY INTERIOR-MUTABILITY FEASIBILITY EXPERIMENT — the Cell→threading
// prototype driven through the kernel-checked threaded-budget lane. This does
// not close or enter the production compiler extraction path.
//
// The clean-kernel `infer_type <-> whnf <-> is_def_eq` cluster mediates its
// budget through an interior-mutable heartbeat `Cell<u32>` reached from
// `&self` — the counter is READ at entry, WRITTEN back decremented, and
// silently carried through every sibling call; it appears in no signature.
// The fuel lanes model that as an EXPLICIT threaded parameter (fuel in,
// remainder out). trust-mir-extract's test-only `cell_threading` module
// explores a state-passing transform over literal synthetic MIR.
//
// This e2e closes the fixture experiment's loop: it loads the drift-gated THREADED artifact
// (`thread_cell_state` applied to the live extraction, byte-pinned by
// trust-mir-extract's `extracted_cell_threaded_artifact_matches_committed`),
// attaches the model=reference postconditions, and drives the
// `threaded_budget_functional` lane — the SAME lane and the SAME clean-kernel
// discharge that the hand-modeled `sn_vs_fuel_resolution_e2e` exercised,
// except here the cluster is DERIVED FROM the cell-mediated MIR rather than
// hand-built in the threaded shape.
//
// HONESTY: the transform is test scaffolding, drift-gated on one side and
// kernel-checked on the other — a wrong transform yields fail-closed emission
// or kernel rejection, never a false certificate. The prototype is
// fixture-grade and has no production consumer: the counter is fuel-shaped
// (`Z | S`) where the real heartbeat
// is `u32` (the standing u32-as-nat modeling step), and the cell-state
// tracking is per-block straight-line (a state-carrying join fails closed).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_certify::threaded_budget_functional::{
    certify_threaded_budget_functional, recheck_threaded_budget_functional,
    threaded_induction_is_load_bearing,
};
use trust_integration_tests::extracted::load_extracted_functions;
use trust_ir::ProofEvidence;
use trust_types::{
    Formula, Sort, SortFromTy, Ty, VcKind, VerifiableFunction, VerificationCondition,
};
use trust_vcgen::threaded_budget_functional::threaded_budget_functional_vcs;

fn property(vc: &VerificationCondition) -> &str {
    match &vc.kind {
        VcKind::FunctionalCorrectness { property, .. } => property,
        other => panic!("expected FunctionalCorrectness, got {other:?}"),
    }
}

/// The model=reference postcondition `m fuel e = r(fuel, e)`. `_0` and the
/// application are the result-pair sort; the arguments are the fuel/payload
/// parameter sorts.
fn ref_post(r: &str, res_sort: &Sort, fuel_sort: &Sort, e_sort: &Sort) -> Formula {
    Formula::Eq(
        Box::new(Formula::var_owned("_0".to_string(), res_sort.clone())),
        Box::new(Formula::FnApp {
            func: r.to_string(),
            args: vec![
                Formula::var_owned("fuel".to_string(), fuel_sort.clone()),
                Formula::var_owned("e".to_string(), e_sort.clone()),
            ],
            sort: res_sort.clone(),
        }),
    )
}

/// Load the THREADED cell-cluster artifact and attach the model=reference
/// postconditions. The bodies are the LITERAL `thread_cell_state` output (the
/// cell reads/writes lowered to the explicit remainder-threaded form) — only
/// the postconditions are attached here (the no_core fixture declares none).
fn threaded_cell_funcs() -> Vec<VerifiableFunction> {
    let mut functions = load_extracted_functions("cell_threaded_functions.json");
    assert_eq!(
        functions.keys().cloned().collect::<Vec<_>>(),
        vec!["fm", "fr", "gm", "gr"],
        "the artifact carries the threaded model cluster and its reference cluster"
    );

    // Sanity: the artifact really is the threaded lane shape (the full pin is
    // trust-mir-extract's drift gate + shape test).
    let fm = &functions["fm"];
    let Ty::Datatype { name: res_name, variants: res_variants } = &fm.body.return_ty else {
        panic!("threaded members return the result pair, got {:?}", fm.body.return_ty);
    };
    assert_eq!(res_name, "res::Res");
    assert_eq!(res_variants.len(), 1, "the pair has one constructor Mk(Fuel, E)");
    let res_sort = Sort::from_ty(&fm.body.return_ty);
    let fuel_param_ty = &fm.body.locals.iter().find(|d| d.index == 1).expect("param _1").ty;
    let Ty::Ref { inner: fuel_dt, .. } = fuel_param_ty else {
        panic!("fuel param must be a reference, got {fuel_param_ty:?}");
    };
    let fuel_sort = Sort::from_ty(fuel_dt);
    let payload_param_ty = &fm.body.locals.iter().find(|d| d.index == 2).expect("param _2").ty;
    let Ty::Ref { inner: e_dt, .. } = payload_param_ty else {
        panic!("payload param must be a reference, got {payload_param_ty:?}");
    };
    let e_sort = Sort::from_ty(e_dt);

    let mut fm = functions.remove("fm").expect("fm");
    let mut gm = functions.remove("gm").expect("gm");
    let fr = functions.remove("fr").expect("fr");
    let gr = functions.remove("gr").expect("gr");
    for f in [&fm, &gm, &fr, &gr] {
        assert!(
            f.postconditions.is_empty(),
            "the no_core fixture declares no spec; the test attaches the properties"
        );
    }
    fm.postconditions = vec![ref_post("fr", &res_sort, &fuel_sort, &e_sort)];
    gm.postconditions = vec![ref_post("gr", &res_sort, &fuel_sort, &e_sort)];
    vec![fm, gm, fr, gr]
}

// ── THE MILESTONE: the interior-mutable Cell-counter cluster, lowered to the
//    threaded shape and discharged model-vs-reference through the clean
//    kernel, end to end ────────────────────────────────────────────────────────

#[test]
fn cell_counter_threaded_cluster_certifies_end_to_end() {
    let funcs = threaded_cell_funcs();

    // 1. VC-GEN: 2 bases + 6 cases + 2 refbases + 6 refcases + the joint
    //    conclusion — the threaded-budget bundle over {fm, gm} vs {fr, gr}.
    let vcs = threaded_budget_functional_vcs(&funcs);
    assert_eq!(vcs.len(), 17, "2 bases + 6 cases + 2 refbases + 6 refcases + conclusion");
    assert!(
        property(&vcs[16])
            .contains("threaded-induction:fuel=fuel::Fuel:Z|S;res=res::Res:Mk;data=expr::E"),
        "the conclusion is marker-bound to the threaded fuel/result/payload datatypes: {}",
        property(&vcs[16])
    );
    // The remainder-threading is present: the M-arm's two-call case names both
    // cluster edges (the second call runs at the first call's remainder).
    let m_case =
        vcs.iter().find(|vc| property(vc) == "threaded_budget_functional_case::fm::M[calls=gm,gm]");
    assert!(
        m_case.is_some(),
        "the two-IH M case is emitted, saw {:#?}",
        vcs.iter().map(property).collect::<Vec<_>>()
    );

    // 2. DISCHARGE: the LITERAL emitted VCs drive the generated majorant
    //    `Fuel.rec` product-motive induction term through the clean kernel.
    let evidence = certify_threaded_budget_functional(&vcs)
        .expect("the threaded cell-cluster model=reference bundle must certify (kernel-checked)");
    let ProofEvidence::CleanCic { term, context, lineage, .. } = &evidence else {
        panic!("expected CleanCic evidence, got {evidence:?}");
    };
    assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
    assert!(
        recheck_threaded_budget_functional(&vcs, term, context, lineage),
        "the serialized certificate must independently re-check via the clean kernel"
    );

    // 3. NO MASQUERADE: the majorant induction is load-bearing — the refl-only
    //    pseudo-proof is kernel-REJECTED against the same goal.
    assert!(
        threaded_induction_is_load_bearing(&vcs),
        "the refl-only pseudo-proof must be REJECTED while the majorant proof is ACCEPTED"
    );

    // 4. TAMPER: one flipped byte in the certificate fails the re-check.
    let mut tampered = term.clone();
    *tampered.last_mut().expect("nonempty term") ^= 0x5a;
    assert!(
        !recheck_threaded_budget_functional(&vcs, &tampered, context, lineage),
        "a tampered certificate must fail the independent re-check"
    );
}
