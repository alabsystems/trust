#![cfg(feature = "ay-backend")]
// §7.2 capability probe: can ay DECIDE a closed BitVec arithmetic-equality
// assertion? `assert!(a+b == b+a)` lowers to the VIOLATION `a+b != b+a`, which
// is UNSAT over BitVec(32) (add is commutative) ⇒ the property holds. If ay
// proves this, the §7.2 fix is purely the missing assert-HOLDS prove-path in the
// verify pass (route the obligation to ay) — NOT an ay limitation.
use trust_router::{InProcessAyBackend, VerificationBackend};
use trust_types::*;

fn bv(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(32))
}

fn assert_vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion { message: "probe".into() },
        function: "ay_cap".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    }
}

#[test]
fn ay_proves_bv32_add_commutativity() {
    let backend = InProcessAyBackend::new();
    // violation of `a+b == b+a`  ⇒  a+b != b+a  (UNSAT ⇒ proved)
    let violation = Formula::Not(Box::new(Formula::Eq(
        Box::new(Formula::BvAdd(Box::new(bv("a")), Box::new(bv("b")), 32)),
        Box::new(Formula::BvAdd(Box::new(bv("b")), Box::new(bv("a")), 32)),
    )));
    let vc = assert_vc(violation);
    let result = backend.verify(&vc);
    eprintln!("[ay-cap] BV32 add-commutativity violation -> {result:?}");
    assert!(
        matches!(&result, VerificationResult::Proved { .. }),
        "ay must DECIDE BV32 add commutativity (UNSAT of the violation); got {result:?}"
    );
}

#[test]
fn ay_does_not_prove_a_wrong_equality() {
    // NEGATIVE control: `a+b == a` is NOT a tautology; its violation `a+b != a`
    // is SAT (e.g. b=1), so ay must NOT prove it (no false-PROVE).
    let backend = InProcessAyBackend::new();
    let violation = Formula::Not(Box::new(Formula::Eq(
        Box::new(Formula::BvAdd(Box::new(bv("a")), Box::new(bv("b")), 32)),
        Box::new(bv("a")),
    )));
    let result = backend.verify(&assert_vc(violation));
    eprintln!("[ay-cap] wrong-equality violation -> {result:?}");
    assert!(
        !matches!(&result, VerificationResult::Proved { .. }),
        "ay must NOT prove a non-tautological equality; got {result:?}"
    );
}
