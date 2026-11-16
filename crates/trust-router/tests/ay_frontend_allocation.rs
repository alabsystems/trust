#![cfg(feature = "ay-backend")]
// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Exercise the native Formula -> AYProgram -> strict proof path. The external
// AY CLI does not participate in this backend and cannot repair its linked AY.

use trust_router::{InProcessAyBackend, VerificationBackend};
use trust_types::{
    AssuranceLevel, Formula, SourceSpan, VcKind, VerificationCondition, VerificationResult,
};

const FIXTURES: [(&str, &str); 3] = [
    (
        include_str!("fixtures/frontend_allocation/allocation-0.json"),
        include_str!("fixtures/frontend_allocation/allocation-0.debug"),
    ),
    (
        include_str!("fixtures/frontend_allocation/allocation-1.json"),
        include_str!("fixtures/frontend_allocation/allocation-1.debug"),
    ),
    (
        include_str!("fixtures/frontend_allocation/allocation-2.json"),
        include_str!("fixtures/frontend_allocation/allocation-2.debug"),
    ),
];

fn verify(index: usize, enlarged_bound: bool) -> VerificationResult {
    let (json, original) = FIXTURES[index];
    let formula: Formula = serde_json::from_str(json).expect("typed frontend formula");
    assert_eq!(format!("{formula:?}"), original.trim_end());
    let formula = if enlarged_bound {
        let mutated = json.replace("{\"Int\":1024}", "{\"Int\":268435456}");
        assert_ne!(mutated, json, "the upper bound must actually change");
        serde_json::from_str(&mutated).expect("typed enlarged-bound formula")
    } else {
        formula
    };
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "allocation limit violation".into() },
        function: "Prober::ensure_num_vars".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    };
    let result = InProcessAyBackend::new().with_timeout(30_000).verify(&vc);
    eprintln!("allocation-{index} enlarged_bound={enlarged_bound}: {result:?}");
    result
}

fn assert_proved(index: usize) {
    let result = verify(index, false);
    assert!(
        matches!(&result, VerificationResult::Proved { strength, .. }
            if strength.assurance == AssuranceLevel::SmtBacked),
        "the exact bounded violation requires a strict checked proof: {result:?}"
    );
}

fn assert_counterexample(index: usize) {
    let result = verify(index, true);
    assert!(
        matches!(result, VerificationResult::Failed { counterexample: Some(_), .. }),
        "the enlarged bound requires a real counterexample, not Unknown: {result:?}"
    );
}

#[test]
fn native_frontend_allocation_u32_is_proved() {
    assert_proved(0);
}

#[test]
fn native_frontend_allocation_i64_is_proved() {
    assert_proved(1);
}

#[test]
fn native_frontend_allocation_bool_is_proved() {
    assert_proved(2);
}

#[test]
fn native_frontend_allocation_u32_large_bound_has_counterexample() {
    assert_counterexample(0);
}

#[test]
fn native_frontend_allocation_i64_large_bound_has_counterexample() {
    assert_counterexample(1);
}

#[test]
fn native_frontend_allocation_bool_large_bound_has_counterexample() {
    assert_counterexample(2);
}
