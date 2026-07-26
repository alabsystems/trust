use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{
    FLOAT_EXP_BOUND_FUEL, contract_exp_bound, f64_finite_biased_exp, float_exp_bound,
    param_place_is_entry_stable, stable_caller_preconditions, substitute_summary_params,
    v2_float_binop_cannot_overflow,
};

const C: i128 = 1_000_000_000_000_000_000; // 1e18, well inside i128 and the Mul margin

/// The f64 sort (`binary64`) a float magnitude bound and its bounded field var
/// carry.
fn f64s() -> Sort {
    Sort::Float { eb: 11, sb: 53 }
}
/// An f64 float-literal precondition term (`FpConst`), as the spec parser emits.
fn fp(v: f64) -> Formula {
    Formula::FpConst { bits: u128::from(v.to_bits()), eb: 11, sb: 53 }
}
fn le(name: &str, c: i128) -> Formula {
    Formula::Le(Box::new(Formula::Var(name.into(), Sort::Int)), Box::new(Formula::Int(c)))
}
fn ge_neg(name: &str, c: i128) -> Formula {
    Formula::Ge(
        Box::new(Formula::Var(name.into(), Sort::Int)),
        Box::new(Formula::Neg(Box::new(Formula::Int(c)))),
    )
}
/// A float-sorted upper bound `<name> <= <c>` (as the parser lowers `x <= 1.0e30`).
fn le_f(name: &str, c: f64) -> Formula {
    Formula::Le(Box::new(Formula::Var(name.into(), f64s())), Box::new(fp(c)))
}
/// A float-sorted lower bound `<name> >= -<c>` (the parser folds the minus into
/// a signed `FpConst`).
fn ge_neg_f(name: &str, c: f64) -> Formula {
    Formula::Ge(Box::new(Formula::Var(name.into(), f64s())), Box::new(fp(-c)))
}
fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// `fn dot(self: _1, o: _2, s: _3) -> _0` whose body computes `self.x * o.x`
/// through the MIR field-copy temps `_5 = copy (_1.0); _6 = copy (_2.0);
/// _4 = Mul(move _5, move _6)`. `reassign_self` appends a `self.x = 1e300`
/// store (the entry-instability that MUST defeat the discharge).
fn dot_like(preconditions: Vec<Formula>, reassign_self: bool) -> VerifiableFunction {
    let mut stmts = vec![
        assign(Place::local(5), Rvalue::Use(Operand::Copy(Place::field(1, 0)))),
        assign(Place::local(6), Rvalue::Use(Operand::Copy(Place::field(2, 0)))),
        assign(
            Place::local(4),
            Rvalue::BinaryOp(
                BinOp::Mul,
                Operand::Move(Place::local(5)),
                Operand::Move(Place::local(6)),
            ),
        ),
    ];
    if reassign_self {
        stmts.push(assign(
            Place::field(1, 0),
            Rvalue::Use(Operand::Constant(ConstValue::Float(1e300))),
        ));
    }
    let local = |index: usize, name: &str| LocalDecl {
        index,
        ty: Ty::f64_ty(),
        name: Some(name.into()),
    };
    VerifiableFunction {
        name: "dot".into(),
        def_path: "Vec3::dot".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                local(0, "_0"),
                local(1, "self"),
                local(2, "o"),
                local(3, "s"),
                local(4, "_4"),
                local(5, "_5"),
                local(6, "_6"),
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 3,
            return_ty: Ty::f64_ty(),
        },
        contracts: vec![],
        preconditions,
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn two_sided() -> Vec<Formula> {
    vec![Formula::And(vec![
        le("self.0", C),
        ge_neg("self.0", C),
        le("o.0", C),
        ge_neg("o.0", C),
        le("s", C),
        ge_neg("s", C),
    ])]
}

#[test]
fn two_sided_param_field_bound_yields_exponent() {
    let func = dot_like(two_sided(), false);
    // self.x (_1.0) and o.x (_2.0) each carry the magnitude exponent of C.
    let expected = f64_finite_biased_exp(C as f64);
    assert_eq!(contract_exp_bound(&func, &Place::field(1, 0)), expected);
    assert_eq!(contract_exp_bound(&func, &Place::field(2, 0)), expected);
    // the bare scalar param `s` (_3) is bounded too.
    assert_eq!(contract_exp_bound(&func, &Place::local(3)), expected);
}

#[test]
fn field_operand_discharges_the_mul_through_the_copy_temp() {
    // The Mul operands are `move _5` / `move _6`; float_exp_bound must recurse
    // through each temp's `Use(Copy(_1.0))` def to the contract-bounded field.
    let func = dot_like(two_sided(), false);
    assert!(
        float_exp_bound(&func, &Operand::Move(Place::local(5)), FLOAT_EXP_BOUND_FUEL).is_some()
    );
    assert!(
        float_exp_bound(&func, &Operand::Move(Place::local(6)), FLOAT_EXP_BOUND_FUEL).is_some()
    );
    assert!(
        v2_float_binop_cannot_overflow(
            &func,
            BinOp::Mul,
            &Operand::Move(Place::local(5)),
            &Operand::Move(Place::local(6)),
        ),
        "self.x * o.x with |field|<=1e18 on both must be provably overflow-free"
    );
}

#[test]
fn bare_param_field_direct_copy_operand_is_bounded() {
    // Under copy-propagated MIR the Mul operand can be `Copy(_1.0)` directly
    // (no temp) — float_exp_bound must still reach contract_exp_bound.
    let func = dot_like(two_sided(), false);
    assert!(
        float_exp_bound(&func, &Operand::Copy(Place::field(1, 0)), FLOAT_EXP_BOUND_FUEL)
            .is_some()
    );
}

#[test]
fn reassigned_param_field_is_not_discharged() {
    // SOUNDNESS: `self.x = 1e300; self.x * o.x` overflows. The entry bound must
    // NOT be applied to the reassigned value, so the Mul stays UNdischarged.
    let func = dot_like(two_sided(), true);
    assert!(!param_place_is_entry_stable(&func, 1), "self is written → not entry-stable");
    assert_eq!(contract_exp_bound(&func, &Place::field(1, 0)), None);
    assert!(
        !v2_float_binop_cannot_overflow(
            &func,
            BinOp::Mul,
            &Operand::Move(Place::local(5)),
            &Operand::Move(Place::local(6)),
        ),
        "a reassigned self.x must keep its overflow obligation"
    );
}

#[test]
fn one_sided_bound_does_not_discharge() {
    // SOUNDNESS: `self.0 <= C` alone leaves the negative magnitude free
    // (self.0 could be -1e300), so no bound may be returned.
    let func = dot_like(vec![Formula::And(vec![le("self.0", C)])], false);
    assert_eq!(contract_exp_bound(&func, &Place::field(1, 0)), None);
}

#[test]
fn non_parameter_local_is_not_matched() {
    // SOUNDNESS: a bound is only honored for a FORMAL PARAMETER place. A field
    // of the temp `_4` (index 4 > arg_count 3) must never be discharged, even
    // if a precondition happened to name "_4.0".
    let func = dot_like(vec![Formula::And(vec![le("_4.0", C), ge_neg("_4.0", C)])], false);
    assert_eq!(contract_exp_bound(&func, &Place::field(4, 0)), None);
}

#[test]
fn unbounded_field_yields_none() {
    let func = dot_like(vec![], false);
    assert_eq!(contract_exp_bound(&func, &Place::field(1, 0)), None);
}

// ---- Trust: FLOAT-literal magnitude bounds (`self.0 <= 1.0e30`) ----

#[test]
fn two_sided_float_field_bound_yields_exponent() {
    // `#[requires(self.0 <= 1.0e30 && self.0 >= -1.0e30 && o.0 <= 1.0e30 && …)]`.
    // The f64 bound 1e30 has biased exponent 1122, and 2*1122 = 2244 < 3000, so
    // the `self.x * o.x` Mul is provably overflow-free.
    let big = 1.0e30_f64;
    let pre = vec![Formula::And(vec![
        le_f("self.0", big),
        ge_neg_f("self.0", big),
        le_f("o.0", big),
        ge_neg_f("o.0", big),
    ])];
    let func = dot_like(pre, false);
    let expected = f64_finite_biased_exp(big);
    assert_eq!(expected, Some(1122), "sanity: 1e30 has biased exp 1122");
    assert_eq!(contract_exp_bound(&func, &Place::field(1, 0)), expected);
    assert_eq!(contract_exp_bound(&func, &Place::field(2, 0)), expected);
    assert!(
        v2_float_binop_cannot_overflow(
            &func,
            BinOp::Mul,
            &Operand::Move(Place::local(5)),
            &Operand::Move(Place::local(6)),
        ),
        "self.x * o.x with |field| <= 1e30 must be provably overflow-free"
    );
}

#[test]
fn one_sided_float_bound_does_not_discharge() {
    // SOUNDNESS: an upper float bound alone leaves the negative magnitude free.
    let func = dot_like(vec![Formula::And(vec![le_f("self.0", 1.0e30)])], false);
    assert_eq!(contract_exp_bound(&func, &Place::field(1, 0)), None);
}

#[test]
fn reassigned_param_field_not_discharged_under_float_bound() {
    // SOUNDNESS: the entry-stability guard is independent of the bound's sort —
    // a body write of self.x defeats a float bound exactly as it defeats an int one.
    let big = 1.0e30_f64;
    let pre = vec![Formula::And(vec![
        le_f("self.0", big),
        ge_neg_f("self.0", big),
        le_f("o.0", big),
        ge_neg_f("o.0", big),
    ])];
    let func = dot_like(pre, true);
    assert_eq!(contract_exp_bound(&func, &Place::field(1, 0)), None);
}

#[test]
fn add_with_one_unbounded_operand_is_not_discharged() {
    // SOUNDNESS (round-10 false-proof): `a + b` must NOT be reported overflow-free
    // when only ONE operand is bounded. `self.0` is bounded to 1e300 (biased exp
    // 2019), but `s` (_3) has NO precondition, so it is unbounded. `1e300 + f64::MAX
    // = +inf` and `1e300 - (-f64::MAX) = +inf`, so the discharge must fail closed and
    // KEEP the obligation. (The former one-sided `||` rule falsely discharged this
    // because the single bounded operand satisfied `e < 2040`.)
    let pre = vec![Formula::And(vec![le_f("self.0", 1.0e300), ge_neg_f("self.0", 1.0e300)])];
    let func = dot_like(pre, false);
    assert_eq!(
        contract_exp_bound(&func, &Place::field(1, 0)),
        Some(2019),
        "sanity: 1e300 has biased exp 2019 (< 2044, so it passes the per-operand check)"
    );
    assert_eq!(
        contract_exp_bound(&func, &Place::local(3)),
        None,
        "the unbounded scalar param `s` has no magnitude bound"
    );
    for op in [BinOp::Add, BinOp::Sub] {
        assert!(
            !v2_float_binop_cannot_overflow(
                &func,
                op,
                &Operand::Copy(Place::field(1, 0)),
                &Operand::Copy(Place::local(3)),
            ),
            "{op:?}: a bounded operand + an UNBOUNDED operand can overflow to inf; \
             the discharge must NOT fire (both operands must be provably bounded)"
        );
    }
}

#[test]
fn add_with_both_operands_bounded_discharges() {
    // The a3d-geom case is preserved: `product1 + product2` with BOTH operands
    // bounded (here both fields at 1e30, biased exp 1122 << 2044) stays provably
    // overflow-free, so the two-sided rule does not regress real discharges.
    let big = 1.0e30_f64;
    let pre = vec![Formula::And(vec![
        le_f("self.0", big),
        ge_neg_f("self.0", big),
        le_f("o.0", big),
        ge_neg_f("o.0", big),
    ])];
    let func = dot_like(pre, false);
    for op in [BinOp::Add, BinOp::Sub] {
        assert!(
            v2_float_binop_cannot_overflow(
                &func,
                op,
                &Operand::Copy(Place::field(1, 0)),
                &Operand::Copy(Place::field(2, 0)),
            ),
            "{op:?}: both operands bounded at 1e30 must stay dischargeable"
        );
    }
}

// ---- Trust: field-projected callee-precondition substitution (edit #3) ----

#[test]
fn field_projected_precond_rebinds_to_actual_field_place() {
    // callee `dot(self, o)` precondition `self.0 <= C && o.0 <= C`; the call
    // `dot(a, a)` binds BOTH formals to the caller place `a`, so both field vars
    // must rebind to the caller's `a.0` (base swapped, `.0` suffix reattached),
    // carrying the callee var's f64 sort.
    let precond = Formula::And(vec![
        Formula::Le(Box::new(Formula::Var("self.0".into(), f64s())), Box::new(fp(1.0e30))),
        Formula::Le(Box::new(Formula::Var("o.0".into(), f64s())), Box::new(fp(1.0e30))),
    ]);
    // The actual for each formal is the caller place `a` (its own sort is
    // irrelevant to the field rebind).
    let replacements = vec![
        ("self".to_string(), Formula::Var("a".into(), Sort::Int)),
        ("o".to_string(), Formula::Var("a".into(), Sort::Int)),
    ];
    let out = substitute_summary_params(&precond, &replacements);
    let expected = Formula::And(vec![
        Formula::Le(Box::new(Formula::Var("a.0".into(), f64s())), Box::new(fp(1.0e30))),
        Formula::Le(Box::new(Formula::Var("a.0".into(), f64s())), Box::new(fp(1.0e30))),
    ]);
    assert_eq!(out, expected);
}

#[test]
fn deref_field_projected_precond_rebinds() {
    // `(*self).2` renders "self*.2"; with self -> the caller place `q` it must
    // become "q*.2" (base swapped, the `*.2` deref-field suffix reattached).
    let precond =
        Formula::Le(Box::new(Formula::Var("self*.2".into(), f64s())), Box::new(fp(1.0e30)));
    let replacements = vec![("self".to_string(), Formula::Var("q".into(), Sort::Int))];
    let out = substitute_summary_params(&precond, &replacements);
    assert_eq!(
        out,
        Formula::Le(Box::new(Formula::Var("q*.2".into(), f64s())), Box::new(fp(1.0e30))),
    );
}

#[test]
fn field_projected_precond_with_nonplace_actual_becomes_free_not_captured() {
    // SOUNDNESS (edit #3): when the actual arg is NOT a place (here an integer
    // constant), the field var must NOT be rebased to any caller place AND must
    // NOT be left spelled `o.0` (which could be captured by a caller's own
    // `o.0`). It becomes a disjoint fresh free var so the caller obligation
    // fails closed.
    let precond =
        Formula::Le(Box::new(Formula::Var("o.0".into(), f64s())), Box::new(fp(1.0e30)));
    let replacements = vec![("o".to_string(), Formula::Int(5))];
    let out = substitute_summary_params(&precond, &replacements);
    let Formula::Le(a, _) = &out else { panic!("expected Le, got {out:?}") };
    let name = a.var_name().expect("lhs is a var");
    assert!(
        name.starts_with("__trust_sigma_field__"),
        "non-place actual must yield a disjoint fresh var, got {name}"
    );
    assert_ne!(name, "o.0", "must never leave the callee formal field name exposed");
}

#[test]
fn non_formal_field_var_is_left_unchanged() {
    // A field var whose base is NOT a substituted formal is untouched (existing
    // behavior): `k.0` with only `self`/`o` in the map stays `k.0`.
    let precond =
        Formula::Le(Box::new(Formula::Var("k.0".into(), f64s())), Box::new(fp(1.0e30)));
    let replacements = vec![("self".to_string(), Formula::Var("a".into(), Sort::Int))];
    let out = substitute_summary_params(&precond, &replacements);
    assert_eq!(out, precond);
}

// ---- Trust: caller's OWN field precondition as a stable hypothesis (edit #4) ----

/// The two-sided float field bounds a `length_sq`-shaped caller declares on its
/// own `self` (`self.0`/`self.1`/…), here just `self.0` for the dot_like shape.
fn caller_self_field_bound() -> Vec<Formula> {
    vec![Formula::And(vec![le_f("self.0", 1.0e30), ge_neg_f("self.0", 1.0e30)])]
}

#[test]
fn caller_field_precondition_admitted_when_base_entry_stable() {
    // The honest length_sq-shaped caller: `#[requires(|self.0| <= 1e30)]`, body
    // never writes self → its OWN field bound is a stable hypothesis, available
    // to discharge a callee's `dot(self, self)` field precondition.
    let func = dot_like(caller_self_field_bound(), false);
    let stable = stable_caller_preconditions(&func);
    assert_eq!(stable.len(), 1, "the entry-stable field precondition must be admitted");
    assert_eq!(stable[0], caller_self_field_bound()[0]);
}

#[test]
fn caller_field_precondition_dropped_when_base_reassigned() {
    // SOUNDNESS (edit #4): a body write of self.x makes the entry bound invalid
    // at later program points, so the field precondition is NOT admitted as a
    // hypothesis (fail-closed) — mirrors the discharge's entry-stability guard.
    let func = dot_like(caller_self_field_bound(), true);
    assert!(!param_place_is_entry_stable(&func, 1));
    assert!(
        stable_caller_preconditions(&func).is_empty(),
        "a reassigned field base must drop the caller field hypothesis"
    );
}

#[test]
fn caller_field_precondition_on_nonparam_base_dropped() {
    // SOUNDNESS: a field of the temp `_4` is not a formal entry value → not an
    // admissible caller hypothesis (rejected fail-closed by the `_`-prefixed /
    // non-source-named base gate, the `place_to_var_name` demotion guarantee).
    let pre = vec![Formula::And(vec![le_f("_4.0", 1.0e30), ge_neg_f("_4.0", 1.0e30)])];
    let func = dot_like(pre, false);
    assert!(stable_caller_preconditions(&func).is_empty());
}
