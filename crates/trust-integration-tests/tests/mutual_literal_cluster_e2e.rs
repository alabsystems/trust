// trust-integration-tests/tests/mutual_literal_cluster_e2e.rs
//
// THE COMBINED LITERAL-CLUSTER FIXTURE, END-TO-END, ON REAL EXTRACTED MIR:
// the three named extensions of the mutual-SCC induction lane — MULTI-IH
// constructors, OPAQUE payload fields, and FUNCTION-VS-FUNCTION (model =
// reference) postconditions — exercised together over the FULL Level shape:
//
//   level::Level = Zero | Succ(*const Level) | Max(*const Level, *const Level)
//                | IMax(*const Level, *const Level) | Param(Name)
//
// (Max/IMax have TWO recursive fields => two IHs per step arm; Param's Name
// field is opaque), fuel-indexed by the nat-shaped `expr::kind::ExprKind =
// Z | S(*const ExprKind)` slice, with a genuine 2-SCC {fm, gm} whose
// postconditions are the `bootstrap_model_fidelity` shape
// `_0 = FnApp(ref, [fuel, e])` against the reference cluster {fr, gr}:
//
//   member (model) style:  fuel-Z base = per-constructor REBUILD;
//   reference style:       fuel-Z base = DIRECT return of `e`;
//   both step legs:        Zero => Zero, Succ x => Succ (next k x),
//                          Max l r => Max (next k l) (next k r),
//                          IMax l r => IMax (next k l) (next k r),
//                          Param n => Param n.
//
// The two clusters are pointwise equal but STRUCTURALLY different folds, so
// the joint statement `forall n, (forall e, fm n e = fr n e) /\ (gm = gr)` is
// a genuine model=reference theorem — discharged by ONE machine-built
// `Fuel.rec` induction with a product motive, `congrArg`+`Eq.trans` chains
// through both IHs of the Max/IMax arms, opaque `Name` atoms bound and never
// inspected, and the reference cluster rebuilt as a second record-motive
// fold. Kernel-checked (`infer_only = false`), round-trip re-checked.
//
// The `VerifiableFunction`s are the LITERAL extractor output, LOADED from the
// committed artifact `fixtures/extracted/literal_cluster_fixture_functions.json`
// — serialized by trust-mir-extract's in-process extraction of the
// literal-cluster fixture (fm/gm model, fr/gr reference, plus the extracted
// NEGATIVE body `gm_wrong`), NOT hand-transcribed. The artifact is
// regenerate-only and DRIFT-GATED: trust-mir-extract's
// `extracted_literal_cluster_artifact_matches_committed` test re-extracts the
// fixture and fails on any byte difference against the committed file, so
// what this test consumes IS what the live extractor produces. The
// postconditions are attached HERE (the no_core fixture declares no
// `#[ensures]`): the spec is the test's declared property, the bodies are the
// literal extracted MIR. This closes the former "extraction serialization"
// residual — the e2e no longer transcribes the extracted shape.
//
// The pipeline is LITERAL: the VCs consumed by trust-certify are exactly the
// values trust-vcgen returns — no shape rebuilding in between.
//
// NO MASQUERADE (kernel-witnessed):
//   * the refl-only pseudo-proof is REJECTED (induction is load-bearing);
//   * the caller-self product-IH projection is REJECTED (the cross-member
//     edges are load-bearing);
//   * WRONG ON ONE BRANCH OF A TWO-IH ARM: `gm_wrong` — the EXTRACTED variant
//     of gm whose IMax step arm rebuilds Max instead of IMax (its MIR differs
//     from gm's in exactly that one aggregate tag, pinned extract-side) —
//     rides the same two lanes in gm's cluster seat and the kernel rejects
//     the WHOLE joint proof — no certificate.
//
// HONESTY / SCOPE: with these three items the lane covers any first-order
// datatype cluster with opaque payloads proving model=reference — the exact
// literal-cluster shape minus SN-vs-fuel (the real kernel cluster's
// termination is SN-based; the fuel-indexed model is the extracted total
// shape), the single named residual.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_certify::mutual_recursive_datatype_functional::{
    certify_mutual_recursive_datatype_functional, cross_member_ih_is_load_bearing,
    mutual_induction_is_load_bearing, recheck_mutual_recursive_datatype_functional,
};
use trust_integration_tests::extracted::load_extracted_functions;
use trust_types::{Formula, Sort, SortFromTy, Ty, VcKind, VerifiableFunction};
use trust_vcgen::mutual_recursive_datatype_functional::mutual_recursive_datatype_functional_vcs;

// ── The extracted full-Level cluster (loaded literal extractor output) ────────

/// The model=reference postcondition `m fuel e = r(fuel, e)`.
fn ref_post(r: &str, fuel_sort: &Sort, level_sort: &Sort) -> Formula {
    Formula::Eq(
        Box::new(Formula::var_owned("_0".to_string(), level_sort.clone())),
        Box::new(Formula::FnApp {
            func: r.to_string(),
            args: vec![
                Formula::var_owned("fuel".to_string(), fuel_sort.clone()),
                Formula::var_owned("e".to_string(), level_sort.clone()),
            ],
            sort: level_sort.clone(),
        }),
    )
}

/// Load the LITERAL extracted cluster and attach the model=reference
/// postconditions. `use_wrong_gm` swaps in the EXTRACTED negative body
/// `gm_wrong` (IMax step arm rebuilds Max) in gm's cluster seat — a
/// name-level substitution only; the body is untouched extractor output.
fn model_vs_reference_funcs(use_wrong_gm: bool) -> Vec<VerifiableFunction> {
    let mut functions = load_extracted_functions("literal_cluster_fixture_functions.json");
    assert_eq!(
        functions.keys().cloned().collect::<Vec<_>>(),
        vec!["fm", "fr", "gm", "gm_wrong", "gr"],
        "the artifact carries the model cluster, the reference cluster, and the negative body"
    );

    // Sanity: the artifact really is the extracted full-Level shape this lane
    // expects (the full pin is the extract-side drift gate).
    let fm = &functions["fm"];
    let Ty::Datatype { name, variants } = &fm.body.return_ty else {
        panic!("cluster members return the modeled Level, got {:?}", fm.body.return_ty);
    };
    assert_eq!(name, "level::Level");
    assert_eq!(
        variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
        vec![("Zero", 0), ("Succ", 1), ("Max", 2), ("IMax", 2), ("Param", 1)],
        "the payload is the FULL Level slice"
    );
    let level_sort = Sort::from_ty(&fm.body.return_ty);
    let fuel_param_ty = &fm.body.locals.iter().find(|d| d.index == 1).expect("param _1").ty;
    let Ty::Ref { inner: fuel_dt, .. } = fuel_param_ty else {
        panic!("fuel param must be a reference, got {fuel_param_ty:?}");
    };
    let fuel_sort = Sort::from_ty(fuel_dt);

    let gm_key = if use_wrong_gm { "gm_wrong" } else { "gm" };
    let mut fm = functions.remove("fm").expect("fm");
    let mut gm = functions.remove(gm_key).expect(gm_key);
    let fr = functions.remove("fr").expect("fr");
    let gr = functions.remove("gr").expect("gr");
    for f in [&fm, &gm, &fr, &gr] {
        assert!(
            f.postconditions.is_empty(),
            "the no_core fixture declares no spec; the test attaches the properties"
        );
    }
    if use_wrong_gm {
        // Seat the extracted negative body as `gm` so fm's cluster edge
        // resolves to it. Name-level only — the MIR body stays literal.
        gm.name = "gm".to_string();
        gm.def_path = "gm".to_string();
    }
    fm.postconditions = vec![ref_post("fr", &fuel_sort, &level_sort)];
    gm.postconditions = vec![ref_post("gr", &fuel_sort, &level_sort)];
    vec![fm, gm, fr, gr]
}

// ── THE MILESTONE: full-Level model-vs-reference, multi-IH + opaque payload,
//    literal extracted MIR, machine-built joint Fuel.rec discharge,
//    kernel-checked, end to end ────────────────────────────────────────────────

#[test]
fn full_level_model_vs_reference_end_to_end() {
    let funcs = model_vs_reference_funcs(false);

    // 1. VC-GEN: per member 5 base + 5 step VCs, the reference definitional
    //    VCs, then the joint tagged conclusion.
    let vcs = mutual_recursive_datatype_functional_vcs(&funcs);
    let props: Vec<&str> = vcs
        .iter()
        .map(|vc| match &vc.kind {
            VcKind::FunctionalCorrectness { property, .. } => property.as_str(),
            other => panic!("expected FunctionalCorrectness, got {other:?}"),
        })
        .collect();
    assert_eq!(
        props,
        vec![
            "mutual_recursive_datatype_functional_base::fm::Zero",
            "mutual_recursive_datatype_functional_base::fm::Succ",
            "mutual_recursive_datatype_functional_base::fm::Max",
            "mutual_recursive_datatype_functional_base::fm::IMax",
            "mutual_recursive_datatype_functional_base::fm::Param",
            "mutual_recursive_datatype_functional_case::fm::Zero[calls=]",
            "mutual_recursive_datatype_functional_case::fm::Succ[calls=gm]",
            "mutual_recursive_datatype_functional_case::fm::Max[calls=gm,gm]",
            "mutual_recursive_datatype_functional_case::fm::IMax[calls=gm,gm]",
            "mutual_recursive_datatype_functional_case::fm::Param[calls=]",
            "mutual_recursive_datatype_functional_base::gm::Zero",
            "mutual_recursive_datatype_functional_base::gm::Succ",
            "mutual_recursive_datatype_functional_base::gm::Max",
            "mutual_recursive_datatype_functional_base::gm::IMax",
            "mutual_recursive_datatype_functional_base::gm::Param",
            "mutual_recursive_datatype_functional_case::gm::Zero[calls=]",
            "mutual_recursive_datatype_functional_case::gm::Succ[calls=fm]",
            "mutual_recursive_datatype_functional_case::gm::Max[calls=fm,fm]",
            "mutual_recursive_datatype_functional_case::gm::IMax[calls=fm,fm]",
            "mutual_recursive_datatype_functional_case::gm::Param[calls=]",
            "mutual_recursive_datatype_functional_refbase::fr",
            "mutual_recursive_datatype_functional_refstep::fr::Zero[calls=]",
            "mutual_recursive_datatype_functional_refstep::fr::Succ[calls=gr]",
            "mutual_recursive_datatype_functional_refstep::fr::Max[calls=gr,gr]",
            "mutual_recursive_datatype_functional_refstep::fr::IMax[calls=gr,gr]",
            "mutual_recursive_datatype_functional_refstep::fr::Param[calls=]",
            "mutual_recursive_datatype_functional_refbase::gr",
            "mutual_recursive_datatype_functional_refstep::gr::Zero[calls=]",
            "mutual_recursive_datatype_functional_refstep::gr::Succ[calls=fr]",
            "mutual_recursive_datatype_functional_refstep::gr::Max[calls=fr,fr]",
            "mutual_recursive_datatype_functional_refstep::gr::IMax[calls=fr,fr]",
            "mutual_recursive_datatype_functional_refstep::gr::Param[calls=]",
            "mutual_recursive_datatype_functional_conclusion[mutual-induction:\
             fuel=expr::kind::ExprKind:Z|S;data=level::Level;members=fm,gm;\
             bases=10;cases=10;refs=fr,gr;refbases=2;refcases=10]",
        ],
        "bundle: {vcs:#?}"
    );

    // 2. DISCHARGE: the LITERAL emitted VCs drive the generated joint
    //    `Fuel.rec` product-motive induction term — two-IH congruence chains
    //    in the Max/IMax minors, opaque Param atoms, and the reference fold —
    //    through the clean kernel.
    let evidence = certify_mutual_recursive_datatype_functional(&vcs)
        .expect("the full-Level model=reference bundle must certify (kernel-checked joint term)");
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
        panic!("expected CleanCic evidence");
    };
    assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
    assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");
    assert!(
        recheck_mutual_recursive_datatype_functional(&vcs, &term, &context, &lineage),
        "the serialized certificate must independently re-check via the clean kernel"
    );

    // 3. NO MASQUERADE: the joint induction and the cross-member product-IH
    //    projections are load-bearing, kernel-witnessed.
    assert!(
        mutual_induction_is_load_bearing(&vcs),
        "the refl-only pseudo-proof must be REJECTED while the Fuel.rec proof is ACCEPTED"
    );
    assert!(
        cross_member_ih_is_load_bearing(&vcs),
        "the caller-self IH projection must be REJECTED while the callee projection is ACCEPTED"
    );
}

// ── NEGATIVE control end-to-end: WRONG ON ONE BRANCH OF A TWO-IH ARM — the
//    EXTRACTED gm_wrong (IMax step arm rebuilds Max) rides the same two lanes
//    and the kernel rejects the WHOLE joint proof ─────────────────────────────

#[test]
fn wrong_branch_of_two_ih_arm_end_to_end_rejected() {
    // gm_wrong's IMax arm rebuilds Max (variant 2) instead of IMax (variant 3):
    // every other arm of every function stays correct (the one-tag delta is
    // pinned by trust-mir-extract's `real_mir_literal_cluster_body_shape`).
    let funcs = model_vs_reference_funcs(true);

    // Emission is spec-driven: the wrong body still emits its bundle (the
    // IMax case VC now concludes with a Max rebuild).
    let vcs = mutual_recursive_datatype_functional_vcs(&funcs);
    assert_eq!(vcs.len(), 33, "the wrong-arm bundle is still emitted, got {vcs:#?}");

    // Discharge: the kernel rejects the joint proof — no certificate for ANY
    // member (mutual induction is all-or-nothing).
    assert!(
        certify_mutual_recursive_datatype_functional(&vcs).is_none(),
        "a two-IH arm wrong in one branch must never certify"
    );
}
