// trust-integration-tests/tests/mutual_recursive_datatype_functional_e2e.rs
//
// WALL C SCALED TO MUTUAL SCCs, END-TO-END: fuel-indexed mutual cluster, REAL
// extracted MIR -> trust-vcgen mutual induction bundle -> trust-certify
// generated joint `Fuel.rec` discharge with a PRODUCT motive, kernel-checked.
//
// The input is a THREE-member ring `fm -> gm -> hm -> fm` — a genuine
// 3-function call-graph SCC, the size and shape of the kernel's
// `infer_type <-> whnf <-> is_def_eq` cluster and of the Aristotle-proved
// template `MutualCluster.lean` (proofs/lean guide: fuel-indexed cluster,
// per-arm step VCs over the uniform IH bundle, base VCs at fuel 0, assembled
// by one joint induction with the AndType product motive). Each member has
// the extracted fuel-indexed form over the def-path-gated `level::Level =
// Zero | Succ(*const Level)` (the nat-shaped fuel) and `expr::kind::ExprKind
// = A | B(*const ExprKind)` (the payload):
//
//   m(Zero, e)   = match e { A => A, B(x) => B(x) }   (identity rebuild)
//   m(Succ k, A) = A
//   m(Succ k, B x) = B (next(k, x))                   (the ring edge)
//
// so the TRUE joint statement is pointwise identity for all three members at
// every fuel — provable ONLY by the mutual induction (each member's step arm
// consumes the NEXT member's IH: the cross-member edges are load-bearing,
// kernel-witnessed below).
//
// The `VerifiableFunction`s are the LITERAL extractor output, LOADED from the
// committed artifact `fixtures/extracted/mutual_fixture_functions.json` —
// serialized by trust-mir-extract's in-process extraction of the ring
// fixture, NOT hand-transcribed. The artifact is regenerate-only and
// DRIFT-GATED: trust-mir-extract's `extracted_mutual_artifact_matches_committed`
// test re-extracts the fixture and fails on any byte difference against the
// committed file, so what this test consumes IS what the live extractor
// produces. The postconditions are attached HERE (the no_core fixture
// declares no `#[ensures]`): the spec is the test's declared property, the
// bodies are the literal extracted MIR. (The mutual lane's fuel gate being
// STRUCTURAL — nat-shape, not name-bound — is witnessed at unit level by the
// deliberately differently-named `fuel::Fuel`/`expr::Expr` hand-built
// fixtures inside trust-vcgen/trust-certify.)
//
// The pipeline exercised here is LITERAL: the VCs consumed by
// `trust_certify::mutual_recursive_datatype_functional` are exactly the values
// `trust_vcgen::mutual_recursive_datatype_functional` returns — no shape
// rebuilding in between.
//
//   1. vcgen detects the SCC of size 3 and emits the mutual bundle: per member
//      2 base VCs (fuel = Zero, per payload constructor) + 2 step VCs (fuel =
//      Succ k, the B case carrying the NEXT member's postcondition as the IH
//      atom, `[calls=..]`-tagged) + the joint `[mutual-induction:..]`
//      conclusion (And of the three per-member statements);
//   2. certify parses the bundle, reconstructs Fuel/Expr, builds the three
//      models as ONE `Fuel.rec` fold over a models record, GENERATES the joint
//      induction proof (product motive; call minors project the callee's
//      component out of the product IH), and the clean kernel checks it
//      (Certified tier), with round-trip recheck;
//   3. no masquerade, kernel-witnessed three ways: the refl-only pseudo-proof
//      is REJECTED (the induction is load-bearing); projecting the WRONG
//      (caller-self) component of the product IH is REJECTED (the CROSS-member
//      edges are load-bearing); and a FALSE postcondition on ONE member (hm)
//      — pushed through the SAME two lanes — kernel-rejects the WHOLE joint
//      proof (mutual induction is all-or-nothing): no certificate.
//
// HONESTY / SCOPE: the recursion primitive SCALED to mutual — still
// fuel-indexed (the real kernel cluster's termination is SN-based; the
// fuel-indexed model IS the extracted total shape, as the template documents).
// The literal `infer_type <-> whnf <-> is_def_eq` discharge additionally needs
// non-datatype payload fields (Param(Name)) and function-vs-function
// postconditions (model = kernel shape) — covered by the sibling
// `mutual_literal_cluster_e2e`.
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

// ── The extracted mutual ring (loaded literal extractor output) ───────────────

/// The TRUE postcondition `m fuel e = e`.
fn identity_post(e_sort: &Sort) -> Formula {
    Formula::Eq(
        Box::new(Formula::var_owned("_0".to_string(), e_sort.clone())),
        Box::new(Formula::var_owned("e".to_string(), e_sort.clone())),
    )
}

/// The FALSE postcondition `m fuel e = B e` (negative control).
fn wrong_b_post(e_sort: &Sort) -> Formula {
    Formula::Eq(
        Box::new(Formula::var_owned("_0".to_string(), e_sort.clone())),
        Box::new(Formula::Ctor {
            ctor: "B".to_string(),
            args: vec![Formula::var_owned("e".to_string(), e_sort.clone())],
            sort: e_sort.clone(),
        }),
    )
}

/// Load the LITERAL extracted 3-member ring and attach per-member
/// postconditions (built against the loaded payload sort).
fn ring(
    post_fm: impl FnOnce(&Sort) -> Formula,
    post_gm: impl FnOnce(&Sort) -> Formula,
    post_hm: impl FnOnce(&Sort) -> Formula,
) -> Vec<VerifiableFunction> {
    let mut functions = load_extracted_functions("mutual_fixture_functions.json");
    assert_eq!(
        functions.keys().cloned().collect::<Vec<_>>(),
        vec!["fm", "gm", "hm"],
        "the artifact carries exactly the ring"
    );

    // Sanity: the artifact really is the extracted mutual shape this lane
    // expects (the full pin is the extract-side drift gate).
    let fm = &functions["fm"];
    let Ty::Datatype { name, variants } = &fm.body.return_ty else {
        panic!("ring members return the modeled payload, got {:?}", fm.body.return_ty);
    };
    assert_eq!(name, "expr::kind::ExprKind");
    assert_eq!(
        variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
        vec![("A", 0), ("B", 1)],
    );
    let e_sort = Sort::from_ty(&fm.body.return_ty);

    let mut out = Vec::new();
    for (name, post) in [
        ("fm", post_fm(&e_sort)),
        ("gm", post_gm(&e_sort)),
        ("hm", post_hm(&e_sort)),
    ] {
        let mut f = functions.remove(name).expect("ring member");
        assert!(
            f.postconditions.is_empty(),
            "the no_core fixture declares no spec; the test attaches the property"
        );
        f.postconditions = vec![post];
        out.push(f);
    }
    out
}

// ── THE MILESTONE: literal extracted mutual-SCC MIR -> mutual induction VCs ->
//    kernel-checked generated joint Fuel.rec discharge, end to end ────────────

#[test]
fn mutual_ring_identity_end_to_end() {
    let funcs = ring(identity_post, identity_post, identity_post);

    // 1. VC-GEN: the mutual bundle — per member 2 base + 2 step VCs, then the
    //    joint tagged conclusion.
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
            "mutual_recursive_datatype_functional_base::fm::A",
            "mutual_recursive_datatype_functional_base::fm::B",
            "mutual_recursive_datatype_functional_case::fm::A[calls=]",
            "mutual_recursive_datatype_functional_case::fm::B[calls=gm]",
            "mutual_recursive_datatype_functional_base::gm::A",
            "mutual_recursive_datatype_functional_base::gm::B",
            "mutual_recursive_datatype_functional_case::gm::A[calls=]",
            "mutual_recursive_datatype_functional_case::gm::B[calls=hm]",
            "mutual_recursive_datatype_functional_base::hm::A",
            "mutual_recursive_datatype_functional_base::hm::B",
            "mutual_recursive_datatype_functional_case::hm::A[calls=]",
            "mutual_recursive_datatype_functional_case::hm::B[calls=fm]",
            "mutual_recursive_datatype_functional_conclusion[mutual-induction:\
             fuel=level::Level:Zero|Succ;data=expr::kind::ExprKind;\
             members=fm,gm,hm;bases=6;cases=6]",
        ],
        "bundle: {vcs:#?}"
    );

    // 2. DISCHARGE: the LITERAL emitted VCs drive the generated joint
    //    `Fuel.rec` product-motive induction term through the clean kernel.
    let evidence = certify_mutual_recursive_datatype_functional(&vcs)
        .expect("the emitted ring-identity bundle must certify (kernel-checked joint term)");
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
        panic!("expected CleanCic evidence");
    };
    assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
    assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");
    assert!(
        recheck_mutual_recursive_datatype_functional(&vcs, &term, &context, &lineage),
        "the serialized certificate must independently re-check via the clean kernel"
    );

    // 3. NO MASQUERADE, twice over: the joint induction is load-bearing (the
    //    refl-only pseudo-proof is kernel-rejected) AND the CROSS-member IH is
    //    load-bearing (projecting the caller's own component of the product IH
    //    instead of the callee's is kernel-rejected).
    assert!(
        mutual_induction_is_load_bearing(&vcs),
        "the refl-only pseudo-proof must be REJECTED while the Fuel.rec proof is ACCEPTED"
    );
    assert!(
        cross_member_ih_is_load_bearing(&vcs),
        "the caller-self IH projection must be REJECTED while the callee projection is ACCEPTED"
    );
}

// ── NEGATIVE control end-to-end: a FALSE postcondition on ONE ring member
//    (same literal extracted bodies) rides the same two lanes and kills the
//    WHOLE bundle at the kernel ────────────────────────────────────────────────

#[test]
fn mutual_ring_wrong_postcondition_on_one_member_end_to_end_rejected() {
    let funcs = ring(identity_post, identity_post, wrong_b_post);

    // Emission is spec-driven: the false spec emits ITS bundle (13 VCs; hm's
    // arms and gm's step-B IH atom carry the wrong rhs).
    let vcs = mutual_recursive_datatype_functional_vcs(&funcs);
    assert_eq!(vcs.len(), 13, "the false spec's bundle is still emitted, got {vcs:#?}");

    // Discharge: the joint proof must be rejected by the clean kernel — no
    // certificate for ANY member (mutual induction is all-or-nothing).
    assert!(
        certify_mutual_recursive_datatype_functional(&vcs).is_none(),
        "a false postcondition on one ring member must never certify"
    );
}
