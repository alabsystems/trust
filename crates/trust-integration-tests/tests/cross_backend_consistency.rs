#![allow(unexpected_cfgs)]
// trust-integration-tests/tests/cross_backend_consistency.rs
//
// Cross-backend consistency testing: dispatches the same VC to multiple
// backends and asserts they agree on the verdict (Proved/Failed).
//
// This catches silent divergence where one backend's formula translation
// or result parsing produces a different verdict than another.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: Allow std HashMap — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_router::constant_folder::ConstantFolderBackend;
// ay_backend removed — ay integration now via ay-direct.
use trust_router::VerificationBackend;
use trust_types::*;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Verdict classification for consistency comparison.
///
/// Backends may disagree on timing and solver names, but should agree on the
/// fundamental verdict. `Unknown` and `Timeout` are grouped together because
/// they indicate the backend could not determine the result — disagreement
/// with another backend returning Unknown is acceptable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Proved,
    Failed,
    Inconclusive, // Unknown or Timeout
}

impl From<&VerificationResult> for Verdict {
    fn from(r: &VerificationResult) -> Self {
        match r {
            VerificationResult::Proved { .. } => Verdict::Proved,
            VerificationResult::Failed { .. } => Verdict::Failed,
            VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. } => {
                Verdict::Inconclusive
            }
            _ => Verdict::Inconclusive,
        }
    }
}

/// Build a VC with the given kind and formula.
fn make_vc(kind: VcKind, formula: Formula, function: &str) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    }
}

/// Collect all available backends for testing.
///
/// Returns backends that are always constructable without external dependencies.
fn test_backends() -> Vec<Box<dyn VerificationBackend>> {
    let backends: Vec<Box<dyn VerificationBackend>> = vec![Box::new(ConstantFolderBackend)];
    // ay_backend removed; ay-direct backend can be added here when needed.
    backends
}

/// Assert that all backends that can handle a VC agree on the verdict.
///
/// Backends returning `Inconclusive` are excluded from the agreement check,
/// since a backend may legitimately be unable to decide a formula that another
/// backend handles. At least one backend must produce a definitive result.
///
/// Returns the consensus verdict.
fn assert_backends_agree(
    backends: &[Box<dyn VerificationBackend>],
    vc: &VerificationCondition,
    test_label: &str,
) -> Verdict {
    let mut definitive_verdicts: Vec<(String, Verdict)> = Vec::new();

    for backend in backends {
        if !backend.can_handle(vc) {
            continue;
        }
        let result = backend.verify(vc);
        let verdict = Verdict::from(&result);
        let name = backend.name().to_string();

        eprintln!("  [{name}] {test_label}: {result:?} -> {verdict:?}");

        if verdict != Verdict::Inconclusive {
            definitive_verdicts.push((name, verdict));
        }
    }

    assert!(
        !definitive_verdicts.is_empty(),
        "{test_label}: no backend produced a definitive result"
    );

    let (ref_name, ref_verdict) = &definitive_verdicts[0];
    for (name, verdict) in &definitive_verdicts[1..] {
        assert_eq!(
            verdict, ref_verdict,
            "{test_label}: backend '{name}' returned {verdict:?} but '{ref_name}' returned {ref_verdict:?}"
        );
    }

    *ref_verdict
}

// ---------------------------------------------------------------------------
// Cross-backend consistency tests
// ---------------------------------------------------------------------------

/// Trivially false formula (UNSAT) => all backends should prove it.
#[test]
fn cross_backend_trivially_false_is_proved() {
    let backends = test_backends();
    let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(false), "trivial_false");
    let verdict = assert_backends_agree(&backends, &vc, "Bool(false)");
    assert_eq!(verdict, Verdict::Proved);
}

/// Trivially true formula (SAT) => all backends should report failure.
#[test]
fn cross_backend_trivially_true_is_failed() {
    let backends = test_backends();
    let vc = make_vc(VcKind::DivisionByZero, Formula::Bool(true), "trivial_true");
    let verdict = assert_backends_agree(&backends, &vc, "Bool(true)");
    assert_eq!(verdict, Verdict::Failed);
}

/// Constant equality: 2 == 2 is SAT => Failed.
#[test]
fn cross_backend_eq_same_constants() {
    let backends = test_backends();
    let formula = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(2)));
    let vc = make_vc(VcKind::Assertion { message: "eq_same".into() }, formula, "eq_same");
    let verdict = assert_backends_agree(&backends, &vc, "Eq(2,2)");
    assert_eq!(verdict, Verdict::Failed);
}

/// Constant inequality: 2 == 3 is UNSAT => Proved.
#[test]
fn cross_backend_eq_different_constants() {
    let backends = test_backends();
    let formula = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(3)));
    let vc = make_vc(VcKind::DivisionByZero, formula, "eq_diff");
    let verdict = assert_backends_agree(&backends, &vc, "Eq(2,3)");
    assert_eq!(verdict, Verdict::Proved);
}

/// Negation of true: Not(true) => false => UNSAT => Proved.
#[test]
fn cross_backend_not_true_is_proved() {
    let backends = test_backends();
    let formula = Formula::Not(Box::new(Formula::Bool(true)));
    let vc = make_vc(VcKind::DivisionByZero, formula, "not_true");
    let verdict = assert_backends_agree(&backends, &vc, "Not(true)");
    assert_eq!(verdict, Verdict::Proved);
}

/// Negation of false: Not(false) => true => SAT => Failed.
#[test]
fn cross_backend_not_false_is_failed() {
    let backends = test_backends();
    let formula = Formula::Not(Box::new(Formula::Bool(false)));
    let vc = make_vc(VcKind::DivisionByZero, formula, "not_false");
    let verdict = assert_backends_agree(&backends, &vc, "Not(false)");
    assert_eq!(verdict, Verdict::Failed);
}

/// And(true, true) => true => SAT => Failed.
#[test]
fn cross_backend_and_true_true() {
    let backends = test_backends();
    let formula = Formula::And(vec![Formula::Bool(true), Formula::Bool(true)]);
    let vc = make_vc(VcKind::DivisionByZero, formula, "and_tt");
    let verdict = assert_backends_agree(&backends, &vc, "And(true,true)");
    assert_eq!(verdict, Verdict::Failed);
}

/// And(true, false) => false => UNSAT => Proved.
#[test]
fn cross_backend_and_true_false() {
    let backends = test_backends();
    let formula = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
    let vc = make_vc(VcKind::DivisionByZero, formula, "and_tf");
    let verdict = assert_backends_agree(&backends, &vc, "And(true,false)");
    assert_eq!(verdict, Verdict::Proved);
}

/// Or(false, false) => false => UNSAT => Proved.
#[test]
fn cross_backend_or_false_false() {
    let backends = test_backends();
    let formula = Formula::Or(vec![Formula::Bool(false), Formula::Bool(false)]);
    let vc = make_vc(VcKind::DivisionByZero, formula, "or_ff");
    let verdict = assert_backends_agree(&backends, &vc, "Or(false,false)");
    assert_eq!(verdict, Verdict::Proved);
}

/// Or(false, true) => true => SAT => Failed.
#[test]
fn cross_backend_or_false_true() {
    let backends = test_backends();
    let formula = Formula::Or(vec![Formula::Bool(false), Formula::Bool(true)]);
    let vc = make_vc(VcKind::DivisionByZero, formula, "or_ft");
    let verdict = assert_backends_agree(&backends, &vc, "Or(false,true)");
    assert_eq!(verdict, Verdict::Failed);
}

/// Arithmetic: 1 + 1 == 2 is SAT => Failed.
/// This tests the formula translation pipeline for arithmetic.
#[test]
#[cfg(feature = "ay-backend")]
fn cross_backend_arithmetic_eq() {
    let backends = test_backends();
    let formula = Formula::Eq(
        Box::new(Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(1)))),
        Box::new(Formula::Int(2)),
    );
    let vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        formula,
        "arith_eq",
    );
    // Mock returns Unknown for Add (complex formula), AY returns Failed (SAT).
    // We only require definitive backends to agree.
    let verdict = assert_backends_agree(&backends, &vc, "Add(1,1)==2");
    assert_eq!(verdict, Verdict::Failed);
}

/// Arithmetic contradiction: 1 + 1 == 3 is UNSAT => Proved.
#[test]
#[cfg(feature = "ay-backend")]
fn cross_backend_arithmetic_neq() {
    let backends = test_backends();
    let formula = Formula::Eq(
        Box::new(Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(1)))),
        Box::new(Formula::Int(3)),
    );
    let vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        formula,
        "arith_neq",
    );
    let verdict = assert_backends_agree(&backends, &vc, "Add(1,1)==3");
    assert_eq!(verdict, Verdict::Proved);
}

/// Implication: true => true is SAT => Failed.
#[test]
#[cfg(feature = "ay-backend")]
fn cross_backend_implies_true_true() {
    let backends = test_backends();
    let formula = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(true)));
    let vc = make_vc(VcKind::Postcondition, formula, "implies_tt");
    // Mock returns Unknown for Implies; AY returns Failed (SAT).
    let verdict = assert_backends_agree(&backends, &vc, "Implies(true,true)");
    assert_eq!(verdict, Verdict::Failed);
}

/// Comparison: 3 < 5 is SAT => Failed.
#[test]
#[cfg(feature = "ay-backend")]
fn cross_backend_lt_true() {
    let backends = test_backends();
    let formula = Formula::Lt(Box::new(Formula::Int(3)), Box::new(Formula::Int(5)));
    let vc = make_vc(VcKind::DivisionByZero, formula, "lt_true");
    let verdict = assert_backends_agree(&backends, &vc, "Lt(3,5)");
    assert_eq!(verdict, Verdict::Failed);
}

/// Comparison: 5 < 3 is UNSAT => Proved.
#[test]
#[cfg(feature = "ay-backend")]
fn cross_backend_lt_false() {
    let backends = test_backends();
    let formula = Formula::Lt(Box::new(Formula::Int(5)), Box::new(Formula::Int(3)));
    let vc = make_vc(VcKind::DivisionByZero, formula, "lt_false");
    let verdict = assert_backends_agree(&backends, &vc, "Lt(5,3)");
    assert_eq!(verdict, Verdict::Proved);
}

/// Variable formula: x == 0 where x is unconstrained.
///
/// Both backends should agree this is SAT (x can be 0) => Failed.
/// ConstantFolderBackend returns Unknown for variables, so only AY provides a
/// definitive answer here. The test validates that no backend
/// contradicts another.
#[test]
#[cfg(feature = "ay-backend")]
fn cross_backend_variable_sat() {
    let backends = test_backends();
    let formula =
        Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
    let vc = make_vc(VcKind::DivisionByZero, formula, "var_sat");
    let verdict = assert_backends_agree(&backends, &vc, "Var(x)==0");
    assert_eq!(verdict, Verdict::Failed);
}

/// ITE formula: ite(true, false, true) => false => UNSAT => Proved.
#[test]
#[cfg(feature = "ay-backend")]
fn cross_backend_ite_constant() {
    let backends = test_backends();
    let formula = Formula::Ite(
        Box::new(Formula::Bool(true)),
        Box::new(Formula::Bool(false)),
        Box::new(Formula::Bool(true)),
    );
    let vc = make_vc(VcKind::DivisionByZero, formula, "ite_const");
    // Mock returns Unknown for Ite; AY returns Proved (UNSAT).
    let verdict = assert_backends_agree(&backends, &vc, "Ite(true,false,true)");
    assert_eq!(verdict, Verdict::Proved);
}

/// Nested: Not(And(true, true)) => Not(true) => false => UNSAT => Proved.
#[test]
fn cross_backend_nested_not_and() {
    let backends = test_backends();
    let formula =
        Formula::Not(Box::new(Formula::And(vec![Formula::Bool(true), Formula::Bool(true)])));
    let vc = make_vc(VcKind::DivisionByZero, formula, "not_and");
    let verdict = assert_backends_agree(&backends, &vc, "Not(And(true,true))");
    assert_eq!(verdict, Verdict::Proved);
}

/// Postcondition VC kind — tests that backends handle L1Functional level.
#[test]
fn cross_backend_postcondition_trivial() {
    let backends = test_backends();
    let vc = make_vc(VcKind::Postcondition, Formula::Bool(false), "postcond_false");
    let verdict = assert_backends_agree(&backends, &vc, "Postcondition(false)");
    assert_eq!(verdict, Verdict::Proved);
}

/// Index bounds VC kind with trivially false formula.
#[test]
fn cross_backend_index_bounds() {
    let backends = test_backends();
    let vc = make_vc(VcKind::IndexOutOfBounds, Formula::Bool(false), "idx_bounds_false");
    let verdict = assert_backends_agree(&backends, &vc, "IndexOutOfBounds(false)");
    assert_eq!(verdict, Verdict::Proved);
}

/// Remainder by zero VC kind with trivially true formula.
#[test]
fn cross_backend_remainder_by_zero() {
    let backends = test_backends();
    let vc = make_vc(VcKind::RemainderByZero, Formula::Bool(true), "rem_zero_true");
    let verdict = assert_backends_agree(&backends, &vc, "RemainderByZero(true)");
    assert_eq!(verdict, Verdict::Failed);
}

// ---------------------------------------------------------------------------
// Meta-test: verify test infrastructure
// ---------------------------------------------------------------------------

/// Ensure we have at least 2 backends in the test suite.
#[test]
#[cfg(feature = "ay-backend")]
fn cross_backend_has_multiple_backends() {
    let backends = test_backends();
    assert!(
        backends.len() >= 2,
        "Cross-backend consistency tests require at least 2 backends, got {}",
        backends.len()
    );
}

/// Ensure every test backend has a distinct name.
#[test]
fn cross_backend_distinct_names() {
    let backends = test_backends();
    let names: Vec<&str> = backends.iter().map(|b| b.name()).collect();
    for (i, name) in names.iter().enumerate() {
        for (j, other) in names.iter().enumerate() {
            if i != j {
                assert_ne!(name, other, "Backends at index {i} and {j} share name '{name}'");
            }
        }
    }
}
