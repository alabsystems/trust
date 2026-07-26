#![cfg(feature = "ay-backend")]
// Probe: can the in-process ay backend PROVE the LIA+Ite modular wrapping-add
// commutativity that trust-vcgen now emits (grounding fix) for
// `assert!(a.wrapping_add(b) == b.wrapping_add(a))`?
//
// The violation (panic-path-feasibility) formula is:
//   _4 != _5
//   ∧ _4 = ite(a+b >= 2^32, a+b - 2^32, a+b)
//   ∧ _5 = ite(b+a >= 2^32, b+a - 2^32, b+a)
//   ∧ 0 <= a < 2^32 ∧ 0 <= b < 2^32
// which is UNSAT (commutativity), so the assert HOLDS. ay's solver decides this
// `unsat` in milliseconds (confirmed via the CLI), so a non-Proved here is a
// strict-proof-checker / deferred-trust coverage gap for LIA+Ite, NOT a solver
// capability gap — exactly the next frontier after the §7.2 BV/array recovery.
use trust_router::{InProcessAyBackend, VerificationBackend};
use trust_types::*;

fn iv(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}
fn modulus() -> Formula {
    Formula::Int(1i128 << 32)
}
fn wrap_add(x: &str, y: &str) -> Formula {
    let s = Formula::Add(Box::new(iv(x)), Box::new(iv(y)));
    Formula::Ite(
        Box::new(Formula::Ge(Box::new(s.clone()), Box::new(modulus()))),
        Box::new(Formula::Sub(Box::new(s.clone()), Box::new(modulus()))),
        Box::new(s),
    )
}
fn range(v: &str) -> Vec<Formula> {
    // Faithful to vcgen's `input_range_constraint`: a NESTED `And([Le(0,v),
    // Le(v, 2^32-1)])` (note: bound is 2^32-1, the modulus is 2^32).
    vec![Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(0)), Box::new(iv(v))),
        Formula::Le(Box::new(iv(v)), Box::new(Formula::Int((1i128 << 32) - 1))),
    ])]
}

fn vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion { message: "probe".into() },
        function: "wrap_commute".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    }
}

#[test]
fn ay_proves_lia_wrapping_add_commutativity() {
    let backend = InProcessAyBackend::new();
    let mut conj = vec![
        Formula::Not(Box::new(Formula::Eq(Box::new(iv("_4")), Box::new(iv("_5"))))),
        Formula::Eq(Box::new(iv("_4")), Box::new(wrap_add("a", "b"))),
        Formula::Eq(Box::new(iv("_5")), Box::new(wrap_add("b", "a"))),
    ];
    conj.extend(range("a"));
    conj.extend(range("b"));
    let result = backend.verify(&vc(Formula::And(conj)));
    eprintln!("[lia-cap] wrapping-add commutativity violation -> {result:?}");
    assert!(
        matches!(&result, VerificationResult::Proved { .. }),
        "ay must PROVE the LIA+Ite modular commutativity (UNSAT of the violation); got {result:?}"
    );
}

#[test]
fn ay_does_not_prove_lia_wrapping_succ_gt() {
    // NEGATIVE control: `a.wrapping_add(1) > a` is FALSE at a == u32::MAX (wraps to
    // 0). Its violation `!(_4 > a)` ∧ `_4 = ite(a+1>=2^32, a+1-2^32, a+1)` ∧ range
    // is SAT (a = 2^32-1), so ay must NOT prove it (the wrap boundary is real).
    let backend = InProcessAyBackend::new();
    let s = Formula::Add(Box::new(iv("a")), Box::new(Formula::Int(1)));
    let wrap = Formula::Ite(
        Box::new(Formula::Ge(Box::new(s.clone()), Box::new(modulus()))),
        Box::new(Formula::Sub(Box::new(s.clone()), Box::new(modulus()))),
        Box::new(s),
    );
    let mut conj = vec![
        // panic when NOT (_4 > a)
        Formula::Not(Box::new(Formula::Gt(Box::new(iv("_4")), Box::new(iv("a"))))),
        Formula::Eq(Box::new(iv("_4")), Box::new(wrap)),
    ];
    conj.extend(range("a"));
    let result = backend.verify(&vc(Formula::And(conj)));
    eprintln!("[lia-cap] wrapping-succ-gt violation -> {result:?}");
    assert!(
        !matches!(&result, VerificationResult::Proved { .. }),
        "ay must NOT prove a non-theorem (wrap at MAX); got {result:?}"
    );
}
