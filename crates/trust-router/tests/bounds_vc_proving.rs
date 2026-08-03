#![cfg(feature = "ay-backend")]
// Regression (ay fa007f8): the exact guarded-index bounds VC formula the
// compiler produces for `if i < 16 { palette[i] }` must PROVE with a
// strict-checked certificate. ay used to solve it UNSAT but export the
// flattened conjunct assumes as unverified `trust` steps, so the strict
// checker rejected the proof and the backend fail-closed to Unknown.
use trust_router::{InProcessAyBackend, VerificationBackend};
use trust_types::*;

fn int_var(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

#[test]
fn guarded_index_bounds_vc_proves_with_certificate() {
    let backend = InProcessAyBackend::new();
    let eq3 = || {
        Formula::Eq(
            Box::new(Formula::Var("_3".into(), Sort::Bool)),
            Box::new(Formula::Lt(Box::new(int_var("i")), Box::new(Formula::Int(16)))),
        )
    };
    let formula = Formula::And(vec![
        eq3(),
        Formula::And(vec![
            Formula::Lt(Box::new(int_var("i")), Box::new(Formula::Int(16))),
            Formula::And(vec![
                eq3(),
                Formula::And(vec![
                    Formula::Eq(
                        Box::new(Formula::Var("_4".into(), Sort::Bool)),
                        Box::new(Formula::Lt(Box::new(int_var("i")), Box::new(Formula::Int(16)))),
                    ),
                    Formula::Ge(Box::new(int_var("i")), Box::new(Formula::Int(16))),
                ]),
            ]),
        ]),
    ]);
    let vc = VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "palette_lookup".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    };
    assert!(backend.can_handle(&vc));
    let result = backend.verify(&vc);
    assert!(
        matches!(&result, VerificationResult::Proved { proof_certificate: Some(c), .. } if !c.is_empty()),
        "guard-conjoined bounds VC must prove with a certificate, got {result:?}"
    );
}

#[test]
fn pure_lia_conflict_proves_with_certificate() {
    let backend = InProcessAyBackend::new();
    let formula = Formula::And(vec![
        Formula::Lt(Box::new(int_var("i")), Box::new(Formula::Int(16))),
        Formula::Ge(Box::new(int_var("i")), Box::new(Formula::Int(16))),
    ]);
    let vc = VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "shape_a".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    };
    let result = backend.verify(&vc);
    assert!(
        matches!(&result, VerificationResult::Proved { .. }),
        "pure LIA conflict must prove, got {result:?}"
    );
}

#[test]
fn bool_eq_guarded_conflict_proves_with_certificate() {
    let backend = InProcessAyBackend::new();
    let formula = Formula::And(vec![
        Formula::Eq(
            Box::new(Formula::Var("_3".into(), Sort::Bool)),
            Box::new(Formula::Lt(Box::new(int_var("i")), Box::new(Formula::Int(16)))),
        ),
        Formula::Lt(Box::new(int_var("i")), Box::new(Formula::Int(16))),
        Formula::Ge(Box::new(int_var("i")), Box::new(Formula::Int(16))),
    ]);
    let vc = VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "shape_b".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    };
    let result = backend.verify(&vc);
    assert!(
        matches!(&result, VerificationResult::Proved { .. }),
        "bool-equality guarded conflict must prove, got {result:?}"
    );
}
