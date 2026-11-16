// Regression: the interval backend must PROVE a guarded signed negation
// (`if x > i32::MIN { -x } else { 0 }`) whose NegationOverflow VC previously
// reached NO deployed safety backend and routed to "no backend can handle this
// VC" -> [negation] UNKNOWN. Signed `-x` overflows iff `x == iW::MIN`, so the
// guard `x > i32::MIN` (operand interval [MIN+1, _]) provably excludes the only
// overflowing value. Two real formula shapes are exercised: the ASSERT path
// (the `Assert{OverflowNeg}` block, goal nested as `Eq(Var, Eq(x,MIN))` asserted
// by a bare `Var`) and the RAW path (`Eq(x,MIN)` as a top-level conjunct). The
// unguarded counterpart MUST still DECLINE (it can overflow).
use trust_router::VerificationBackend;
use trust_router::interval_backend::IntervalBackend;
use trust_types::*;

const I32_MIN: i128 = -2147483648;

/// Trust: 2026-09-19 — the VC now carries the `ObligationRecord` trust-vcgen
/// really emits, because the interval lane now binds the negation goal to
/// `subject` rather than taking the first `Eq(_, type_min)` among the conjuncts.
///
/// That scan was a FALSE PROVE channel: a HYPOTHESIS can carry that shape, and in
/// a function with more than one negation it routinely does — `if a >= lim { -a }`
/// with `lim` folded to `i64::MIN` was proved from the OTHER negation's operand
/// `_4 == 2^62` while ay refuted the row at `a == i64::MIN`
/// (`interval_backend::tests::a_foreign_operands_min_comparison_is_not_this_rows_negation_goal`).
/// Both negation emitters record the negated operand as `subject`, renamed at the
/// same construction point the body is, so it is byte-identical to the operand's
/// occurrence in `formula`; a VC built without one is not a shape vcgen produces,
/// and an unauthenticated goal declines.
fn negation_vc_for(formula: Formula, subject: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } },
        function: "neg".to_string().into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: Some(ObligationRecord {
            body: Formula::Bool(true),
            wrappers: Vec::new(),
            subject: Some(subject),
            width: Some(32),
        }),
    }
}

fn iv(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}
fn bv(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Bool)
}
fn gt(a: Formula, b: Formula) -> Formula {
    Formula::Gt(Box::new(a), Box::new(b))
}
fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}

#[test]
fn guarded_negation_assert_path_proves_via_interval() {
    // Mirrors the real vcgen formula for `if x > i32::MIN { -x } else { 0 }`
    // (assert path, width 32): defs + guard + the asserted is-min flag. There is
    // NO input_range_constraint conjunct (the assert path omits it) — the guard
    // alone supplies the lower bound that excludes i32::MIN.
    let x = iv("x");
    let formula = Formula::And(vec![
        eq(bv("gt#s0_0"), gt(x.clone(), Formula::Int(I32_MIN))), // gt#s0_0 := x > MIN
        gt(x.clone(), Formula::Int(I32_MIN)),                    // threaded path guard
        eq(bv("is_min#s1_0"), eq(x.clone(), Formula::Int(I32_MIN))), // is_min := (x == MIN)
        bv("is_min#s1_0"),                                       // GOAL: assert is_min
    ]);
    let vc = negation_vc_for(formula, x);
    assert!(
        IntervalBackend.can_handle(&vc),
        "guarded -x (assert path) must prove no negation overflow"
    );
}

#[test]
fn guarded_negation_raw_path_proves_via_interval() {
    // Raw path: the violation goal Eq(x, MIN) is a top-level conjunct alongside
    // the guard. Must also prove.
    let x = iv("x");
    let formula = Formula::And(vec![
        gt(x.clone(), Formula::Int(I32_MIN)), // guard x > MIN
        eq(x.clone(), Formula::Int(I32_MIN)), // raw violation goal: x == MIN
    ]);
    let vc = negation_vc_for(formula, x);
    assert!(
        IntervalBackend.can_handle(&vc),
        "guarded -x (raw path) must prove no negation overflow"
    );
}

#[test]
fn unguarded_negation_does_not_prove() {
    // SOUNDNESS guard: with NO `x > i32::MIN` guard, the operand can equal i32::MIN
    // so `-x` CAN overflow. The interval includes MIN -> must DECLINE.
    let x = iv("x");
    let formula = Formula::And(vec![
        // input range only: MIN <= x <= MAX (contains MIN)
        Formula::Le(Box::new(Formula::Int(I32_MIN)), Box::new(x.clone())),
        Formula::Le(Box::new(x.clone()), Box::new(Formula::Int(2147483647))),
        eq(x.clone(), Formula::Int(I32_MIN)), // violation goal: x == MIN
    ]);
    let vc = negation_vc_for(formula, x);
    assert!(
        !IntervalBackend.can_handle(&vc),
        "unguarded -x CAN overflow at i32::MIN; must not prove"
    );
}
