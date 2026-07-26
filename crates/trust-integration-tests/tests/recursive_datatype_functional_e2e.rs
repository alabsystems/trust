// trust-integration-tests/tests/recursive_datatype_functional_e2e.rs
//
// WALL C END-TO-END: recursive-datatype-function induction, REAL extracted
// MIR -> trust-vcgen induction bundle -> trust-certify generated `.rec`
// discharge, kernel-checked.
//
// The input `VerifiableFunction` is the LITERAL extractor output for the
// fixture `mirror : &Level -> Level` (`level::Level = Zero | Succ(*const
// Level)`, zero -> zero, succ p -> succ (mirror p)), LOADED from the
// committed artifact `fixtures/extracted/mirror_fixture_functions.json` —
// serialized by trust-mir-extract's in-process extraction run, NOT
// hand-transcribed. The artifact is regenerate-only and DRIFT-GATED:
// trust-mir-extract's `extracted_mirror_artifact_matches_committed` test
// re-extracts the fixture and fails on any byte difference against the
// committed file, so what this test consumes IS what the live extractor
// produces. (The former hand-transcription of the extracted shape survives
// as the unit-level fixtures inside trust-vcgen/trust-certify.)
//
// The postcondition is attached HERE, by the test: the no_core fixture
// carries no `#[ensures]` attribute, so the artifact's `postconditions` is
// empty — the spec is the test's declared property, the BODY is the literal
// extracted MIR.
//
// The pipeline exercised here is LITERAL: the VCs consumed by
// `trust_certify::recursive_datatype_functional` are exactly the values
// `trust_vcgen::recursive_datatype_functional` returns — no shape rebuilding
// in between.
//
//   1. vcgen emits the induction bundle for the declared postcondition
//      `mirror l = l`: per-constructor cases (the Succ case carrying the IH
//      `__ih0` in place of the recursive call) + the `[induction:..]`-tagged
//      conclusion;
//   2. certify parses the bundle, reconstructs the datatype, builds the model
//      as a `Level.rec` fold, GENERATES the `.rec` induction proof, and the
//      clean kernel checks it (Certified tier), with round-trip recheck;
//   3. no masquerade: the refl-only pseudo-proof is kernel-REJECTED for the
//      same bundle (the IH is load-bearing), and the FALSE postcondition
//      `mirror l = Succ l` — pushed through the SAME two lanes — is
//      kernel-rejected at discharge (no certificate).
//
// SCOPE: the recursion PRIMITIVE (self-recursive, single parameter, nullary /
// unary-recursive constructors). The mutual `infer_type <-> whnf <-> is_def_eq`
// cluster additionally needs mutual induction over the SCC, multi-IH
// constructors (Max/IMax), and non-datatype payloads — covered by the sibling
// mutual/literal-cluster e2e lanes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_certify::recursive_datatype_functional::{
    certify_recursive_datatype_functional, induction_is_load_bearing,
    recheck_recursive_datatype_functional,
};
use trust_integration_tests::extracted::load_extracted_functions;
use trust_types::{Formula, Sort, SortFromTy, Ty, VcKind, VerifiableFunction};
use trust_vcgen::recursive_datatype_functional::recursive_datatype_functional_vcs;

// ── The extracted mirror fixture (loaded literal extractor output) ───────────

/// Load the LITERAL extracted `mirror` and attach the test's postcondition
/// (built against the loaded function's own Level sort).
fn extracted_mirror_func(make_post: impl FnOnce(&Sort) -> Formula) -> VerifiableFunction {
    let mut functions = load_extracted_functions("mirror_fixture_functions.json");
    let mut f = functions.remove("mirror").expect("artifact contains mirror");

    // Sanity: the artifact really is the extracted recursive shape this lane
    // expects (the full pin is the extract-side drift gate).
    let Ty::Datatype { name, variants } = &f.body.return_ty else {
        panic!("mirror returns the modeled Level datatype, got {:?}", f.body.return_ty);
    };
    assert_eq!(name, "level::Level");
    assert_eq!(
        variants.iter().map(|(c, fs)| (c.as_str(), fs.len())).collect::<Vec<_>>(),
        vec![("Zero", 0), ("Succ", 1)],
    );
    assert_eq!(f.body.arg_count, 1);
    assert!(
        f.postconditions.is_empty(),
        "the no_core fixture declares no spec; the test attaches the property"
    );

    let level_sort = Sort::from_ty(&f.body.return_ty);
    f.postconditions = vec![make_post(&level_sort)];
    f
}

/// The TRUE postcondition `mirror l = l`.
fn identity_post(level_sort: &Sort) -> Formula {
    Formula::Eq(
        Box::new(Formula::var_owned("_0".to_string(), level_sort.clone())),
        Box::new(Formula::var_owned("l".to_string(), level_sort.clone())),
    )
}

/// The FALSE postcondition `mirror l = Succ l` (negative control).
fn wrong_succ_post(level_sort: &Sort) -> Formula {
    Formula::Eq(
        Box::new(Formula::var_owned("_0".to_string(), level_sort.clone())),
        Box::new(Formula::Ctor {
            ctor: "Succ".to_string(),
            args: vec![Formula::var_owned("l".to_string(), level_sort.clone())],
            sort: level_sort.clone(),
        }),
    )
}

// ── THE MILESTONE: literal extracted MIR -> induction VCs -> kernel-checked
//    generated .rec discharge, end to end ─────────────────────────────────────

#[test]
fn recursive_mirror_identity_end_to_end() {
    let func = extracted_mirror_func(identity_post);

    // 1. VC-GEN: the induction bundle (2 cases + tagged conclusion).
    let vcs = recursive_datatype_functional_vcs(&func);
    assert_eq!(vcs.len(), 3, "Zero case + Succ case + conclusion, got {vcs:#?}");
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
            "recursive_datatype_functional_case::Zero",
            "recursive_datatype_functional_case::Succ",
            "recursive_datatype_functional_conclusion[induction:level::Level;cases=2]",
        ]
    );

    // 2. DISCHARGE: the LITERAL emitted VCs drive the generated `.rec`
    //    induction term through the clean kernel.
    let evidence = certify_recursive_datatype_functional(&vcs)
        .expect("the emitted mirror-identity bundle must certify (kernel-checked .rec term)");
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
        panic!("expected CleanCic evidence");
    };
    assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
    assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");
    assert!(
        recheck_recursive_datatype_functional(&vcs, &term, &context, &lineage),
        "the serialized certificate must independently re-check via the clean kernel"
    );

    // 3. NO MASQUERADE: the discharge genuinely needed the IH — the refl-only
    //    pseudo-proof of the same goal is kernel-rejected.
    assert!(
        induction_is_load_bearing(&vcs),
        "the refl-only pseudo-proof must be REJECTED while the .rec proof is ACCEPTED"
    );
}

// ── NEGATIVE control end-to-end: a FALSE postcondition on the SAME literal
//    extracted body rides the same two lanes and dies at the kernel ───────────

#[test]
fn recursive_mirror_wrong_postcondition_end_to_end_rejected() {
    let func = extracted_mirror_func(wrong_succ_post);

    // Emission is spec-driven: the false spec emits ITS bundle (3 VCs).
    let vcs = recursive_datatype_functional_vcs(&func);
    assert_eq!(vcs.len(), 3, "the false spec's bundle is still emitted, got {vcs:#?}");

    // Discharge: the generated proof for the false postcondition must be
    // rejected by the clean kernel — no certificate is minted.
    assert!(
        certify_recursive_datatype_functional(&vcs).is_none(),
        "the false postcondition `mirror l = Succ l` must never certify"
    );
}
