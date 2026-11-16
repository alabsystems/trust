use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Sort, SourceSpan,
    Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
};

use super::generate_vcs;

fn overflow_vc_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(
                &vc.kind,
                VcKind::ArithmeticOverflow { .. } | VcKind::UncheckedArithmeticOverflow { .. }
            )
        })
        .count()
}

/// True if the rendered formula mentions `name` — used to confirm a
/// conjoined precondition reaches the VC formula (so the solver can
/// discharge it) without running an SMT solver in the unit test.
fn formula_mentions_var(f: &Formula, name: &str) -> bool {
    f.to_smtlib().contains(name)
}

/// `fn(receiver: ty) -> ty { receiver.pow(exp) }` as a single-block tail
/// call. The receiver lowers to the first MIR arg (local 1); the exponent is
/// the constant `exp`. `pre` optionally adds an entry precondition.
fn pow_func(ty: Ty, exp: i128, pre: Vec<Formula>) -> VerifiableFunction {
    VerifiableFunction {
        name: "pow_caller".to_string(),
        def_path: "test::pow_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("n".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "core::num::<impl i32>::pow".to_string(),
                    args: vec![
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(exp as u128, 32)),
                    ],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key("core::num::<impl i32>::pow"),
                    is_foreign: false,
                },
            }],
            arg_count: 1,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: pre,
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `base.pow(exp)` with BOTH base and exponent constant.
fn const_pow_func(ty: Ty, base: i128, exp: i128) -> VerifiableFunction {
    let mut f = pow_func(ty, exp, vec![]);
    if let Terminator::Call { args, .. } = &mut f.body.blocks[0].terminator {
        args[0] = Operand::Constant(ConstValue::Int(base));
    }
    f
}

/// `unchecked_OP(a, b)` over two `ty` params (locals 1 and 2). `pre` adds an
/// optional entry precondition.
fn unchecked_func(op: &str, ty: Ty, pre: Vec<Formula>) -> VerifiableFunction {
    VerifiableFunction {
        name: "unchecked_caller".to_string(),
        def_path: "test::unchecked_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: format!("core::intrinsics::{op}"),
                    args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(
                        &format!("core::intrinsics::{op}").to_string(),
                    ),
                    is_foreign: false,
                },
            }],
            arg_count: 2,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: pre,
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

// ----- pow: fire on bug -----

#[test]
fn flags_unguarded_pow() {
    // `n.pow(2)` with `n` an unbounded i32 param can overflow (any
    // `n > 46341`), but lowers to a Call with no BinaryOp — it was reported
    // vacuously safe. It must now produce an ArithmeticOverflow obligation.
    let func = pow_func(Ty::i32(), 2, vec![]);
    assert_eq!(
        overflow_vc_count(&func),
        1,
        "unguarded `n.pow(2)` must emit an ArithmeticOverflow obligation"
    );
}

#[test]
fn flags_provably_overflowing_const_pow() {
    // `10i32.pow(20)` overflows i32 at compile time; the non-const-eval path
    // must fail closed rather than slip a known overflow through.
    let func = const_pow_func(Ty::i32(), 10, 20);
    assert_eq!(
        overflow_vc_count(&func),
        1,
        "a constant pow that provably overflows must be flagged"
    );
}

// ----- pow: no false positive -----

#[test]
fn allows_small_const_pow() {
    // `2u32.pow(3)` == 8 fits in u32: provably safe, no obligation at all
    // (mirrors the const-size allocation skip).
    let func = const_pow_func(Ty::u32(), 2, 3);
    assert_eq!(
        overflow_vc_count(&func),
        0,
        "a constant pow that provably fits must produce no obligation"
    );
}

#[test]
fn allows_pow_exp_one() {
    // `n.pow(1)` == n: cannot overflow regardless of `n`. No obligation.
    let func = pow_func(Ty::i32(), 1, vec![]);
    assert_eq!(
        overflow_vc_count(&func),
        0,
        "`n.pow(1)` is the identity and must produce no overflow obligation"
    );
}

#[test]
fn bounded_pow_carries_precondition_for_discharge() {
    // `#[requires(n < 100)] n.pow(2)` is safe (`99*99 = 9801` fits i32). The
    // obligation IS generated, but its formula must carry the precondition
    // `n < 100` so the solver discharges it — the safe/buggy distinction.
    let pre =
        Formula::Lt(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(100)));
    let func = pow_func(Ty::i32(), 2, vec![pre]);
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
        .expect("bounded pow still generates the obligation (discharged at solve time)");
    assert!(
        formula_mentions_var(&vc.formula, "n"),
        "the pow overflow VC must reference the bounded operand `n` so the \
         precondition `n < 100` can discharge it; formula: {:?}",
        vc.formula
    );
    // The conjoined precondition literal `100` must be present.
    assert!(
        vc.formula.to_smtlib().contains("100"),
        "the bound `n < 100` must be conjoined into the pow overflow VC, formula: {:?}",
        vc.formula
    );
}

// ----- unchecked_{add,sub,mul}: fire on bug -----

#[test]
fn flags_unchecked_add() {
    // `unchecked_add(a, b)` is UB on overflow; unguarded u32 args can overflow.
    let func = unchecked_func("unchecked_add", Ty::u32(), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(
            vc.kind,
            VcKind::UncheckedArithmeticOverflow { op: BinOp::Add, .. }
        )),
        "unguarded `unchecked_add(a, b)` must emit an Add ArithmeticOverflow obligation"
    );
}

#[test]
fn flags_unchecked_sub() {
    let func = unchecked_func("unchecked_sub", Ty::u32(), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(
            vc.kind,
            VcKind::UncheckedArithmeticOverflow { op: BinOp::Sub, .. }
        )),
        "unguarded `unchecked_sub(a, b)` must emit a Sub ArithmeticOverflow obligation"
    );
}

#[test]
fn flags_unchecked_mul() {
    let func = unchecked_func("unchecked_mul", Ty::u32(), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(
            vc.kind,
            VcKind::UncheckedArithmeticOverflow { op: BinOp::Mul, .. }
        )),
        "unguarded `unchecked_mul(a, b)` must emit a Mul ArithmeticOverflow obligation"
    );
}

// ----- unchecked_*: no false positive -----

#[test]
fn guarded_unchecked_add_carries_precondition() {
    // A `#[requires(a < 10 && b < 10)]`-guarded `unchecked_add(a, b)` is safe.
    // The obligation is generated but must carry the precondition so the
    // solver discharges it (`a + b <= 18 < u32::MAX`).
    let pre = Formula::And(vec![
        Formula::Lt(Box::new(Formula::Var("a".into(), Sort::Int)), Box::new(Formula::Int(10))),
        Formula::Lt(Box::new(Formula::Var("b".into(), Sort::Int)), Box::new(Formula::Int(10))),
    ]);
    let func = unchecked_func("unchecked_add", Ty::u32(), vec![pre]);
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::UncheckedArithmeticOverflow { op: BinOp::Add, .. }))
        .expect("guarded unchecked_add still generates the obligation");
    assert!(
        formula_mentions_var(&vc.formula, "a") && formula_mentions_var(&vc.formula, "b"),
        "the unchecked_add overflow VC must reference both operands so the \
         precondition can discharge it; formula: {:?}",
        vc.formula
    );
}

#[test]
fn ignores_ordinary_call() {
    // An ordinary (non-arithmetic) call must not produce any overflow
    // obligation — the recognizer must not broadly fail-close on every Call.
    let func = unchecked_func("helper_compute", Ty::u32(), vec![]);
    assert_eq!(
        overflow_vc_count(&func),
        0,
        "a non-arithmetic call must not produce an overflow obligation"
    );
}

// ----- pow: the exact overflow model (POW-SYMEXP-1, 2026-10-05) -----
//
// The symbolic-exponent arm used to build `base >= 2 AND exp >= W` (`W - 1`
// signed) — a condition that GUARANTEES overflow, used as the
// satisfiable-iff-violation body. A negative base or an exponent bounded below
// the width made it UNSAT, so `(-2i32).pow(e)` and `if e < 32 { b.pow(e) }`
// were PROVED (kernel-certified) while `3u32.pow(21)` panics. Every body is now
// exact; these tests compare it against core's own `checked_pow`.

/// `fn(b: ty, e: u32) -> ty { BASE.pow(EXP) }`: `BASE` is the param `b`
/// (local 1) or a literal, `EXP` the param `e` (local 2) or a literal.
fn pow_sym_func(
    ty: Ty,
    base: Option<i128>,
    exp: Option<u32>,
    pre: Vec<Formula>,
) -> VerifiableFunction {
    let signed = ty.is_signed();
    let width = ty.int_width().expect("an integer type");
    let base_op = match base {
        None => Operand::Copy(Place::local(1)),
        Some(v) if signed => Operand::Constant(ConstValue::Int(v)),
        Some(v) => Operand::Constant(ConstValue::Uint(v as u128, width)),
    };
    let exp_op = match exp {
        None => Operand::Copy(Place::local(2)),
        Some(v) => Operand::Constant(ConstValue::Uint(u128::from(v), 32)),
    };
    let callee = format!("core::num::<impl {}>::pow", if signed { "i32" } else { "u32" });
    VerifiableFunction {
        name: "pow_sym_caller".to_string(),
        def_path: "test::pow_sym_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("e".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.clone(),
                    args: vec![base_op, exp_op],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(&callee),
                    is_foreign: false,
                },
            }],
            arg_count: 2,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: pre,
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The raw violation body the pow arm builds (before any caller conjoin).
fn pow_body(func: &VerifiableFunction) -> Option<Formula> {
    let Terminator::Call { args, dest, .. } = &func.body.blocks[0].terminator else {
        unreachable!("pow_sym_func builds a call")
    };
    super::v2_overflow_call_body(func, super::OverflowCall::Pow, args, dest).map(|r| r.0)
}

/// Core's own answer: does `b.pow(e)` panic (`checked_pow` is `None`) for the
/// integer type `(width, signed)`? A `b` outside the type is not a question.
fn pow_overflows(width: u32, signed: bool, b: i128, e: u32) -> bool {
    macro_rules! native {
        ($t:ty) => {
            <$t>::try_from(b).expect("test base must be in the type").checked_pow(e).is_none()
        };
    }
    match (width, signed) {
        (8, false) => native!(u8),
        (8, true) => native!(i8),
        (16, false) => native!(u16),
        (16, true) => native!(i16),
        (32, false) => native!(u32),
        (32, true) => native!(i32),
        (64, false) => native!(u64),
        (64, true) => native!(i64),
        (128, false) => native!(u128),
        (128, true) => native!(i128),
        _ => unreachable!("no such integer type"),
    }
}

fn in_type(width: u32, signed: bool, b: i128) -> bool {
    if signed {
        (crate::range::signed_min(width)..=crate::range::signed_max(width)).contains(&b)
    } else {
        b >= 0 && u128::try_from(b).is_ok_and(|v| v <= crate::range::unsigned_max(width))
    }
}

fn int_ty(width: u32, signed: bool) -> Ty {
    Ty::Int { width, signed }
}

/// A tiny evaluator for the formula shapes the pow arm builds. Values above
/// `i128::MAX` (only `u128::MAX` in a range conjunct) saturate, which is exact
/// for every comparison against the `i128`-sized test values used here.
fn eval_int(f: &Formula, env: &[(&str, i128)]) -> i128 {
    let var = |name: &str| {
        env.iter()
            .find(|(n, _)| *n == name)
            .map(|(_, v)| *v)
            .unwrap_or_else(|| panic!("unbound variable `{name}` in {}", f.to_smtlib()))
    };
    match f {
        Formula::Int(v) => *v,
        Formula::UInt(v) => i128::try_from(*v).unwrap_or(i128::MAX),
        Formula::Var(name, _) => var(name),
        Formula::SymVar(sym, _) => var(sym.as_str()),
        Formula::Mul(a, b) => {
            eval_int(a, env).checked_mul(eval_int(b, env)).expect("test product must fit i128")
        }
        Formula::Neg(a) => -eval_int(a, env),
        other => panic!("not an integer term: {}", other.to_smtlib()),
    }
}

fn eval_bool(f: &Formula, env: &[(&str, i128)]) -> bool {
    let cmp = |a: &Formula, b: &Formula| (eval_int(a, env), eval_int(b, env));
    match f {
        Formula::Bool(v) => *v,
        Formula::Not(a) => !eval_bool(a, env),
        Formula::And(cs) => cs.iter().all(|c| eval_bool(c, env)),
        Formula::Or(cs) => cs.iter().any(|c| eval_bool(c, env)),
        Formula::Implies(a, b) => !eval_bool(a, env) || eval_bool(b, env),
        Formula::Eq(a, b) => {
            let (x, y) = cmp(a, b);
            x == y
        }
        Formula::Lt(a, b) => {
            let (x, y) = cmp(a, b);
            x < y
        }
        Formula::Le(a, b) => {
            let (x, y) = cmp(a, b);
            x <= y
        }
        Formula::Gt(a, b) => {
            let (x, y) = cmp(a, b);
            x > y
        }
        Formula::Ge(a, b) => {
            let (x, y) = cmp(a, b);
            x >= y
        }
        other => panic!("not a boolean the pow arm builds: {}", other.to_smtlib()),
    }
}

const ALL_INT_TYPES: [(u32, bool); 10] = [
    (8, false),
    (8, true),
    (16, false),
    (16, true),
    (32, false),
    (32, true),
    (64, false),
    (64, true),
    (128, false),
    (128, true),
];

#[test]
fn pow_fitting_base_interval_table_edges() {
    use super::pow_fitting_base_interval as iv;
    // `(-2)^31 == i32::MIN` fits; `2^31` does not.
    assert_eq!(iv(32, true, 31), (-2, 1));
    assert_eq!(iv(32, false, 31), (0, 2));
    assert_eq!(iv(32, false, 2), (0, 65_535));
    assert_eq!(iv(32, true, 2), (-46_340, 46_340));
    // `2^63 == |i64::MIN|` is a cube: the odd-k lower end is one wider.
    assert_eq!(iv(64, true, 3), (-2_097_152, 2_097_151));
    assert_eq!(iv(8, true, 7), (-2, 1));
    assert_eq!(iv(8, true, 3), (-5, 5));
    assert_eq!(iv(128, false, 2), (0, i128::from(u64::MAX)));
    assert_eq!(iv(128, true, 127), (-2, 1));
    assert_eq!(iv(64, false, 63), (0, 2));
    assert_eq!(iv(64, false, 64), (0, 1));
    assert_eq!(iv(32, true, 32), (-1, 1));
    assert_eq!(iv(32, false, u32::MAX), (0, 1));
}

#[test]
fn pow_fitting_base_interval_matches_checked_pow_at_both_ends() {
    // For every type and every exponent, `hi` fits and `hi + 1` overflows; for a
    // signed type, `lo` fits and `lo - 1` overflows. Core decides, not the table.
    for (width, signed) in ALL_INT_TYPES {
        for k in 2..=width + 2 {
            let (lo, hi) = super::pow_fitting_base_interval(width, signed, k);
            assert!(
                !pow_overflows(width, signed, hi, k),
                "{width}/{signed} k={k}: hi={hi} must fit"
            );
            if in_type(width, signed, hi + 1) {
                assert!(
                    pow_overflows(width, signed, hi + 1, k),
                    "{width}/{signed} k={k}: hi+1={} must overflow",
                    hi + 1
                );
            }
            if signed {
                assert!(
                    !pow_overflows(width, signed, lo, k),
                    "{width}/{signed} k={k}: lo={lo} must fit"
                );
                if in_type(width, signed, lo - 1) {
                    assert!(
                        pow_overflows(width, signed, lo - 1, k),
                        "{width}/{signed} k={k}: lo-1={} must overflow",
                        lo - 1
                    );
                }
            } else {
                assert_eq!(lo, 0);
            }
        }
    }
}

#[test]
fn pow_literal_base_threshold_matches_checked_pow() {
    for (width, signed) in ALL_INT_TYPES {
        let max = i128::try_from(crate::range::unsigned_max(width)).unwrap_or(i128::MAX);
        let mut bases = vec![0, 1, 2, 3, 7, 10, 255, 1000, 65_536];
        if signed {
            bases.extend([-1, -2, -3, -7, -10, -1000]);
            bases.extend([crate::range::signed_min(width), crate::range::signed_max(width)]);
        } else {
            bases.push(max);
        }
        for b in bases.into_iter().filter(|b| in_type(width, signed, *b)) {
            let t = super::pow_literal_base_overflow_threshold(b, width, signed);
            for e in 0..=width + 3 {
                let modeled = t.is_some_and(|t| e >= t);
                assert_eq!(
                    modeled,
                    pow_overflows(width, signed, b, e),
                    "{width}/{signed}: {b}^{e}, threshold {t:?}"
                );
            }
        }
    }
    // `2u128.pow(127)` fits `u128`: the unsigned threshold is computed in `u128`.
    assert_eq!(super::pow_literal_base_overflow_threshold(2, 128, false), Some(128));
    assert_eq!(super::pow_literal_base_overflow_threshold(-2, 32, true), Some(32));
    assert_eq!(super::pow_literal_base_overflow_threshold(2, 32, true), Some(31));
    // A literal that is not a value of the type charges every exponent.
    assert_eq!(super::pow_literal_base_overflow_threshold(256, 8, false), Some(0));
    assert_eq!(super::pow_literal_base_overflow_threshold(-1, 8, false), Some(0));
}

/// Every shape of `base.pow(exp)` — symbolic or literal base, symbolic or literal
/// exponent — over every 8-bit value and every exponent up to past the width:
/// the body holds exactly when core's `checked_pow` overflows.
#[test]
fn pow_body_is_exact_over_every_8_bit_case() {
    for signed in [false, true] {
        let ty = int_ty(8, signed);
        let bases: Vec<i128> = if signed { (-128..=127).collect() } else { (0..=255).collect() };
        let exps = 0..=12u32;
        // symbolic base, symbolic exponent
        let body = pow_body(&pow_sym_func(ty.clone(), None, None, vec![]))
            .expect("a symbolic pow always carries a row");
        for &b in &bases {
            for e in exps.clone() {
                assert_eq!(
                    eval_bool(&body, &[("b", b), ("e", i128::from(e))]),
                    pow_overflows(8, signed, b, e),
                    "signed={signed} b={b} e={e} (symbolic/symbolic): {}",
                    body.to_smtlib()
                );
            }
        }
        // literal base, symbolic exponent
        for &b in &bases {
            let body = pow_body(&pow_sym_func(ty.clone(), Some(b), None, vec![]));
            for e in exps.clone() {
                let modeled = body.as_ref().is_some_and(|f| eval_bool(f, &[("e", i128::from(e))]));
                assert_eq!(
                    modeled,
                    pow_overflows(8, signed, b, e),
                    "signed={signed} {b}^e at e={e}"
                );
            }
        }
        // symbolic base, literal exponent (the unroll up to the width, then the
        // fitting-base model above it)
        for e in exps.clone() {
            let body = pow_body(&pow_sym_func(ty.clone(), None, Some(e), vec![]));
            for &b in &bases {
                let modeled = body.as_ref().is_some_and(|f| eval_bool(f, &[("b", b)]));
                assert_eq!(
                    modeled,
                    pow_overflows(8, signed, b, e),
                    "signed={signed} b^{e} at b={b}"
                );
            }
        }
        // both literal: no row iff it fits, the fail-closed `true` row iff not
        for &b in &bases {
            for e in exps.clone() {
                let body = pow_body(&pow_sym_func(ty.clone(), Some(b), Some(e), vec![]));
                if pow_overflows(8, signed, b, e) {
                    assert!(matches!(body, Some(Formula::Bool(true))), "{b}^{e} must fail closed");
                } else {
                    assert!(body.is_none(), "{b}^{e} fits: no row");
                }
            }
        }
    }
}

/// The 16-bit symbolic body over every base and every exponent past the width.
#[test]
fn pow_body_is_exact_over_every_16_bit_base() {
    for signed in [false, true] {
        let body = pow_body(&pow_sym_func(int_ty(16, signed), None, None, vec![]))
            .expect("a symbolic pow always carries a row");
        let bases: Vec<i128> =
            if signed { (-32_768..=32_767).collect() } else { (0..=65_535).collect() };
        for b in bases {
            for e in 0..=17u32 {
                assert_eq!(
                    eval_bool(&body, &[("b", b), ("e", i128::from(e))]),
                    pow_overflows(16, signed, b, e),
                    "signed={signed} b={b} e={e}"
                );
            }
        }
    }
}

/// The wide types at every interval edge (and the type's own extremes), every
/// exponent up to past the width.
#[test]
fn pow_body_is_exact_at_the_interval_edges_of_wide_types() {
    for (width, signed) in ALL_INT_TYPES.into_iter().filter(|(w, _)| *w >= 32) {
        let body = pow_body(&pow_sym_func(int_ty(width, signed), None, None, vec![]))
            .expect("a symbolic pow always carries a row");
        for e in 0..=width + 2 {
            let (lo, hi) =
                if e >= 2 { super::pow_fitting_base_interval(width, signed, e) } else { (0, 0) };
            let mut probes = vec![lo - 1, lo, lo + 1, hi - 1, hi, hi + 1, -2, -1, 0, 1, 2, 3];
            if signed {
                probes.extend([crate::range::signed_min(width), crate::range::signed_max(width)]);
            } else {
                probes.push(i128::try_from(crate::range::unsigned_max(width)).unwrap_or(i128::MAX));
            }
            for b in probes.into_iter().filter(|b| in_type(width, signed, *b)) {
                assert_eq!(
                    eval_bool(&body, &[("b", b), ("e", i128::from(e))]),
                    pow_overflows(width, signed, b, e),
                    "{width}/{signed}: b={b} e={e}"
                );
            }
        }
    }
}

fn pow_row_verdicts(func: &VerifiableFunction) -> Vec<trust_types::VerificationResult> {
    let router = crate::test_router::deterministic_test_router();
    generate_vcs(func)
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
        .map(|vc| {
            router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
        })
        .collect()
}

fn lt(name: &str, v: i128) -> Formula {
    Formula::Lt(Box::new(Formula::Var(name.into(), Sort::Int)), Box::new(Formula::Int(v)))
}

fn assert_pow_refuted(what: &str, func: &VerifiableFunction) {
    let verdicts = pow_row_verdicts(func);
    assert!(
        verdicts.iter().any(|r| matches!(r, trust_types::VerificationResult::Failed { .. })),
        "{what} panics for some input: its pow row must be REFUTED, got {verdicts:?}"
    );
}

fn assert_pow_proved(what: &str, func: &VerifiableFunction) {
    let verdicts = pow_row_verdicts(func);
    assert!(!verdicts.is_empty(), "{what}: the pow row must still be minted");
    assert!(
        verdicts.iter().all(|r| matches!(r, trust_types::VerificationResult::Proved { .. })),
        "{what} never panics: its pow row must be PROVED, got {verdicts:?}"
    );
}

#[test]
fn a_negative_literal_base_with_a_symbolic_exponent_is_refuted() {
    // `(-2i32).pow(e)` panics at `e == 32`; `(-3i64).pow(e)` at `e == 40`.
    assert_pow_refuted("(-2i32).pow(e)", &pow_sym_func(Ty::i32(), Some(-2), None, vec![]));
    assert_pow_refuted("(-3i64).pow(e)", &pow_sym_func(int_ty(64, true), Some(-3), None, vec![]));
}

#[test]
fn an_exponent_bounded_below_the_width_does_not_discharge_a_symbolic_base() {
    // `e < 32 => b.pow(e)` (u32) panics at `3u32.pow(21)`.
    assert_pow_refuted(
        "e < 32 => b.pow(e) (u32)",
        &pow_sym_func(Ty::u32(), None, None, vec![lt("e", 32)]),
    );
    // `e < 8 => b.pow(e)` (u64) panics at `1000u64.pow(7)`.
    assert_pow_refuted(
        "e < 8 => b.pow(e) (u64)",
        &pow_sym_func(int_ty(64, false), None, None, vec![lt("e", 8)]),
    );
    // `b < 0 && e < 31 => b.pow(e)` (i32) panics at `(-3i32).pow(21)`.
    assert_pow_refuted(
        "b < 0 && e < 31 => b.pow(e) (i32)",
        &pow_sym_func(Ty::i32(), None, None, vec![lt("b", 0), lt("e", 31)]),
    );
    // `b < 2 => b.pow(e)` (i32): every negative base with `|b| >= 2` overflows.
    assert_pow_refuted(
        "b < 2 => b.pow(e) (i32)",
        &pow_sym_func(Ty::i32(), None, None, vec![lt("b", 2)]),
    );
}

#[test]
fn a_constant_exponent_above_the_width_charges_a_negative_base() {
    // `b < 0 => b.pow(70)` (i64): always overflows for `b <= -2`.
    assert_pow_refuted(
        "b < 0 => b.pow(70) (i64)",
        &pow_sym_func(int_ty(64, true), None, Some(70), vec![lt("b", 0)]),
    );
    // Both literal: `(-2i32).pow(40)` always panics — the fail-closed row.
    assert!(
        matches!(
            pow_body(&pow_sym_func(Ty::i32(), Some(-2), Some(40), vec![])),
            Some(Formula::Bool(true))
        ),
        "(-2i32).pow(40) must carry the fail-closed row"
    );
    // ... while `(-2i32).pow(31) == i32::MIN` fits: no row at all.
    assert!(pow_body(&pow_sym_func(Ty::i32(), Some(-2), Some(31), vec![])).is_none());
}

#[test]
fn guards_that_exclude_every_overflow_still_discharge_the_pow_row() {
    // The controls that were (correctly) proved before stay proved.
    assert_pow_proved(
        "e < 32 => 2u32.pow(e)",
        &pow_sym_func(Ty::u32(), Some(2), None, vec![lt("e", 32)]),
    );
    assert_pow_proved(
        "e < 31 => 2i32.pow(e)",
        &pow_sym_func(Ty::i32(), Some(2), None, vec![lt("e", 31)]),
    );
    assert_pow_proved(
        "e < 128 => 2u128.pow(e)",
        &pow_sym_func(int_ty(128, false), Some(2), None, vec![lt("e", 128)]),
    );
    // Newly provable: a guard bounding BOTH operands (`9^4 == 6561`).
    assert_pow_proved(
        "b < 10 && e < 5 => b.pow(e) (u32)",
        &pow_sym_func(Ty::u32(), None, None, vec![lt("b", 10), lt("e", 5)]),
    );
    // A base in `{0, 1}` never overflows, whatever the exponent.
    assert_pow_proved(
        "b < 2 => b.pow(e) (u32)",
        &pow_sym_func(Ty::u32(), None, None, vec![lt("b", 2)]),
    );
}

/// `certify` reads an ay `Proved` that the clean kernel does not re-check as
/// `Unknown`, so a guarded `pow` keeps its certify verdict only if the new body
/// stays kernel-certifiable. Pinned for the literal-base controls (whose body is
/// the same single atom shape as before) and for a symbolic base under a guard on
/// both operands, which takes the new disjunctive body.
#[test]
fn guarded_pow_rows_stay_kernel_certified() {
    let cases = [
        ("e < 32 => 2u32.pow(e)", pow_sym_func(Ty::u32(), Some(2), None, vec![lt("e", 32)])),
        ("e < 31 => 2i32.pow(e)", pow_sym_func(Ty::i32(), Some(2), None, vec![lt("e", 31)])),
        (
            "b < 10 && e < 5 => b.pow(e) (u32)",
            pow_sym_func(Ty::u32(), None, None, vec![lt("b", 10), lt("e", 5)]),
        ),
        (
            "-10 < b < 10 && e < 5 => b.pow(e) (i32)",
            pow_sym_func(
                Ty::i32(),
                None,
                None,
                vec![
                    lt("b", 10),
                    Formula::Gt(
                        Box::new(Formula::Var("b".into(), Sort::Int)),
                        Box::new(Formula::Int(-10)),
                    ),
                    lt("e", 5),
                ],
            ),
        ),
    ];
    for (what, func) in cases {
        let vcs = generate_vcs(&func);
        let rows: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
            .collect();
        assert_eq!(rows.len(), 1, "{what}: one pow row");
        assert!(
            trust_certify::certify_vc(rows[0]).is_some(),
            "{what}: the guarded pow row must stay kernel-certified; formula: {}",
            rows[0].formula.to_smtlib()
        );
    }
}

#[test]
fn ignores_pow_on_non_integer() {
    // `x.pow(2)` where the receiver is a float-ish/unknown type the int model
    // cannot apply to must be skipped, not flagged.
    let func = pow_func(Ty::Float { width: 64 }, 2, vec![]);
    assert_eq!(
        overflow_vc_count(&func),
        0,
        "pow on a non-integer receiver must not produce an integer overflow obligation"
    );
}

// ----- pow: only core's primitive-integer `pow` owes its row (2026-10-06) -----
//
// POW-SYMEXP-1 integration review: `overflow_arith_call` classified a callee as
// `OverflowCall::Pow` by its last path segment alone, so a USER function or
// method named `pow` returning an integer was charged std's overflow row over
// its own arguments. Once the body became exact, the user calls that the old
// body happened to leave UNSAT under a guard or with a negative literal base
// (`if e < 40 { pow(-2, e) }`, `if e < 32 { m.pow(e) }`) were refuted too — a
// counterexample for an overflow that cannot happen (measured on the stage 1 of
// `9e11546767`). The `pow` arm now requires `numeric_panic::int_inherent`'s
// authenticated `core::num::<impl iN/uN>::pow`, as `strict_pow` does.

/// `func` with its call's callee replaced by `callee` (the structured key
/// follows the spelling, as the extractor's does).
fn with_pow_callee(mut func: VerifiableFunction, callee: &str) -> VerifiableFunction {
    if let Terminator::Call { func: f, callee_key, .. } = &mut func.body.blocks[0].terminator {
        *f = callee.to_string();
        *callee_key = crate::sep_engine::tests::fixture_key(callee);
    }
    func
}

#[test]
fn a_user_fn_or_method_named_pow_mints_no_pow_row() {
    // The measured shapes: `fp` (`e < 40`, literal `-2`), `upg` (`e < 32`), and
    // the unguarded `up`, which was refuted even under the old body.
    let shapes = [
        ("e < 40 => pow(-2, e) (i32)", pow_sym_func(Ty::i32(), Some(-2), None, vec![lt("e", 40)])),
        ("e < 32 => m.pow(e) (u32)", pow_sym_func(Ty::u32(), None, None, vec![lt("e", 32)])),
        ("m.pow(e) (u32)", pow_sym_func(Ty::u32(), None, None, vec![])),
    ];
    for callee in [
        "pow",
        "userpow::pow",
        "userpow::M::pow",
        "<userpow::M as userpow::Pow>::pow",
        "num_traits::pow::Pow::pow",
        // A user module mimicking core's owner spelling has no sysroot root.
        "userpow::num::<impl u32>::pow",
        // A stamp in front of anything but core's exact spelling is refused (a stamped
        // `core::num::<impl u32>::pow` is the genuine core in a graph that stamps it,
        // and keeps its row: `a_stamped_genuine_core_keeps_its_pow_and_unchecked_rows`).
        "__trust_crate@1973d11b2baa21fa::userpow::num::<impl u32>::pow",
        "__trust_crate@1973d11b2baa21fa::core::num::wrapping::Wrapping::<u32>::pow",
    ] {
        assert!(
            super::alloc_bounds::overflow_arith_call(callee).is_none(),
            "`{callee}` is not core's integer `pow` and must not be classified as it"
        );
        for (what, func) in &shapes {
            assert_eq!(
                overflow_vc_count(&with_pow_callee(func.clone(), callee)),
                0,
                "{what} through `{callee}`: a user `pow` must mint no overflow row"
            );
        }
    }
}

#[test]
fn core_primitive_int_pow_keeps_its_row_and_the_deny_list_keeps_its_answer() {
    // Every spelling of core's own `pow` is still classified, including the
    // `std::num::` owner. (The extractor's `::<__trust_args@…>` fingerprint is
    // only appended to a callee with generic arguments, which `pow` has none of;
    // the old tail match did not read that spelling either.)
    for callee in [
        "core::num::<impl u32>::pow",
        "core::num::<impl i32>::pow",
        "core::num::<impl u8>::pow",
        "core::num::<impl usize>::pow",
        "core::num::<impl isize>::pow",
        "core::num::<impl i128>::pow",
        "std::num::<impl u64>::pow",
    ] {
        assert!(
            matches!(
                super::alloc_bounds::overflow_arith_call(callee),
                Some(super::OverflowCall::Pow)
            ),
            "`{callee}` is core's integer `pow` and must keep its overflow row"
        );
    }
    // ... and still mints and refutes through it.
    assert_pow_refuted(
        "e < 32 => b.pow(e) (u32), std spelling",
        &with_pow_callee(
            pow_sym_func(Ty::u32(), None, None, vec![lt("e", 32)]),
            "std::num::<impl u32>::pow",
        ),
    );
    // The `unchecked_*` arms keep every authenticated spelling (UNCHECKED-NAME-1,
    // 2026-10-06, narrowed them like `pow`; see the tests below) ...
    for (callee, op) in [
        ("core::intrinsics::unchecked_add", BinOp::Add),
        ("core::num::<impl u32>::unchecked_sub", BinOp::Sub),
    ] {
        assert!(
            matches!(
                super::alloc_bounds::overflow_arith_call(callee),
                Some(super::OverflowCall::Unchecked(o)) if o == op
            ),
            "`{callee}` keeps its unchecked-arithmetic classification"
        );
    }
    // ... and a bare `unchecked_mul` (no owner at all) no longer mints, while the
    // name-only view the deny-list reads still names it.
    assert!(super::alloc_bounds::overflow_arith_call("unchecked_mul").is_none());
    assert!(matches!(
        super::alloc_bounds::overflow_arith_call_name_only("unchecked_mul"),
        Some(super::OverflowCall::Unchecked(BinOp::Mul))
    ));
    // The deny-list union reads the name-only view: a sysroot `pow` that is not
    // the integer inherent one (`Wrapping`, `Saturating`) mints no row, but is
    // still withheld as a fn-item type argument, exactly as before.
    for callee in [
        "core::num::wrapping::Wrapping::<u32>::pow",
        "core::num::saturating::Saturating::<u32>::pow",
    ] {
        assert!(
            super::alloc_bounds::overflow_arith_call(callee).is_none(),
            "`{callee}` mints no row"
        );
        assert!(
            super::alloc_bounds::overflow_arith_call_name_only(callee).is_some()
                && super::callee_has_call_site_panic_family(callee),
            "`{callee}`: the deny-list answer must not move"
        );
    }
}

// ----- unchecked_{add,sub,mul}: only core's own operation owes the row (2026-10-06) -----
//
// UNCHECKED-NAME-1: the `unchecked_*` arms of `overflow_arith_call` were decided by the
// last path segment alone, the defect POW-SYMEXP-1's review closed for `pow`. A USER
// function or method merely NAMED `unchecked_add` (its body `a ^ b`) was charged
// `UncheckedArithmeticOverflow` over its own arguments: an unguarded caller was refused
// with an `unknown` row, and a guarded one (`a < 10 && b < 10`) read `proved |
// clean-kernel-certified | unchecked arithmetic overflow (Add)` for an addition the
// program never performs (measured on the stage 1 of `9e11546767`). The arms now
// require `numeric_panic::int_inherent`'s authenticated `core::num::<impl iN/uN>::…`,
// or the exact `core::intrinsics::unchecked_*` path under an authenticated root.

/// The `UncheckedArithmeticOverflow { op }` rows `func` mints.
fn unchecked_vc_count(func: &VerifiableFunction, op: BinOp) -> usize {
    generate_vcs(func)
        .iter()
        .filter(
            |vc| matches!(vc.kind, VcKind::UncheckedArithmeticOverflow { op: o, .. } if o == op),
        )
        .count()
}

#[test]
fn a_user_fn_or_method_named_unchecked_op_mints_no_row() {
    let guarded = || vec![Formula::And(vec![lt("a", 10), lt("b", 10)])];
    for (callee, op) in [
        // `pub fn unchecked_add(a: u32, b: u32) -> u32 { a ^ b }` and its siblings, as
        // the extractor renders a call to them (scout probes `u2.rs` / `u4.rs`).
        ("u2::unchecked_add", BinOp::Add),
        ("u2::unchecked_mul", BinOp::Mul),
        ("u2::M::unchecked_sub", BinOp::Sub),
        // `impl T for u32 { fn unchecked_mul(self, b: u32) -> u32 }`: the trait route.
        ("<u32 as u4::T>::unchecked_mul", BinOp::Mul),
        // No owner at all.
        ("unchecked_add", BinOp::Add),
        // A user module mimicking core's owner spelling has no sysroot root.
        ("my::num::<impl u32>::unchecked_sub", BinOp::Sub),
        ("mycore::intrinsics::unchecked_add", BinOp::Add),
        // A stamp in front of anything but core's exact inherent spelling is refused;
        // the intrinsic half stays authenticated-only (a stamped
        // `core::num::<impl u32>::unchecked_add` is the genuine core in a graph that
        // stamps it: `a_stamped_genuine_core_keeps_its_pow_and_unchecked_rows`).
        ("__trust_crate@1973d11b2baa21fa::my::num::<impl u32>::unchecked_add", BinOp::Add),
        ("__trust_crate@1973d11b2baa21fa::core::intrinsics::unchecked_mul", BinOp::Mul),
    ] {
        // The planted premise: the tail-only view still names every spelling, so the
        // old arm (`kind @ Unchecked(_) => Some(kind)`) minted for each of them.
        assert!(
            matches!(
                super::alloc_bounds::overflow_arith_call_name_only(callee),
                Some(super::OverflowCall::Unchecked(o)) if o == op
            ),
            "premise: `{callee}` is an unchecked_* name"
        );
        assert!(
            super::alloc_bounds::overflow_arith_call(callee).is_none(),
            "`{callee}` is not core's `unchecked_*` and must not be classified as it"
        );
        let leaf = callee.rsplit("::").next().unwrap();
        for (what, pre) in [("unguarded", vec![]), ("a < 10 && b < 10", guarded())] {
            assert_eq!(
                unchecked_vc_count(
                    &with_pow_callee(unchecked_func(leaf, Ty::u32(), pre), callee),
                    op
                ),
                0,
                "{what} `{callee}(a, b)`: a user function mints no unchecked-overflow row"
            );
        }
        // The fn-item deny-list keeps the name-only answer.
        assert!(
            super::callee_has_call_site_panic_family(callee),
            "`{callee}`: the deny-list answer must not move"
        );
    }
}

#[test]
fn core_unchecked_ops_keep_their_rows() {
    for (callee, op) in [
        ("core::num::<impl u32>::unchecked_add", BinOp::Add),
        ("core::num::<impl i32>::unchecked_sub", BinOp::Sub),
        ("core::num::<impl u64>::unchecked_mul", BinOp::Mul),
        ("core::num::<impl usize>::unchecked_add", BinOp::Add),
        ("core::num::<impl i128>::unchecked_mul", BinOp::Mul),
        ("std::num::<impl u32>::unchecked_sub", BinOp::Sub),
        ("core::intrinsics::unchecked_add", BinOp::Add),
        ("core::intrinsics::unchecked_sub", BinOp::Sub),
        ("std::intrinsics::unchecked_mul", BinOp::Mul),
    ] {
        assert!(
            matches!(
                super::alloc_bounds::overflow_arith_call(callee),
                Some(super::OverflowCall::Unchecked(o)) if o == op
            ),
            "`{callee}` is core's own UB-on-overflow operation and keeps its row"
        );
        let leaf = callee.rsplit("::").next().unwrap();
        assert_eq!(
            unchecked_vc_count(
                &with_pow_callee(unchecked_func(leaf, Ty::u32(), vec![]), callee),
                op
            ),
            1,
            "unguarded `{callee}(a, b)` mints exactly one unchecked-overflow row"
        );
    }
    // A leaf that is not the arm's own operation never mints (the name-only view
    // answers `None` for both, so neither the old nor the new arm reaches them).
    for callee in [
        "core::num::<impl u32>::unchecked_add::precondition_check",
        "core::num::<impl u32>::unchecked_shl",
        "core::intrinsics::unchecked_div",
    ] {
        assert!(super::alloc_bounds::overflow_arith_call(callee).is_none(), "`{callee}`");
    }
    // `NonZero::<u32>::unchecked_add` is core's but not a primitive inherent: no row,
    // as before the change (MEASURED on the stage 1 of `9e11546767`: its operand is the
    // `NonZero` ADT, so the old arm's body built nothing; the call is refused by the
    // `[unsafe:unmodeled-call]` row instead).
    assert!(
        super::alloc_bounds::overflow_arith_call(
            "core::num::nonzero::NonZero::<u32>::unchecked_add"
        )
        .is_none()
    );
}

// ----- a stamped GENUINE core keeps the rows (wave-19 review, 2026-10-09) -----
//
// The extractor stamps the real core when a second crate named `core` is in the graph
// (`trust_types::sysroot_identity_stamp_required`, rule 1) and under `-Zbuild-std`
// (rule 2). UNCHECKED-NAME-1 and ABS-NAME-1 (and, before them, POW-SYMEXP-1) anchored
// these arms on `numeric_panic::int_inherent`, which refuses every stamp, so a genuine
// call lost its row in such a graph: MEASURED on the stage 1 of `46e9afaf95` beside a
// verify-off `--crate-name core` dependency, `unsafe { a.unchecked_add(b) }` lost its
// `unchecked_overflow` row (present on the stage 1 of `f39efe05ca`), and `x.abs()` lost
// its refuted `negation` row, so the default build went from exit 1 to exit 0 and the
// binary panicked on `i32::MIN`. The minting arms now read core's exact spelling behind
// ONE well-formed leading stamp (`numeric_panic::int_inherent_minting`).

/// The stable crate id the extractor stamped core with in the measured graph.
const STAMP: &str = "__trust_crate@414739228a72f04f::";

#[test]
fn a_stamped_genuine_core_keeps_its_pow_and_unchecked_rows() {
    let pow = format!("{STAMP}core::num::<impl u32>::pow");
    assert!(
        matches!(super::alloc_bounds::overflow_arith_call(&pow), Some(super::OverflowCall::Pow)),
        "`{pow}` is core's `pow` in a graph that stamps core"
    );
    assert_pow_refuted(
        "e < 32 => b.pow(e) (u32), stamped core",
        &with_pow_callee(pow_sym_func(Ty::u32(), None, None, vec![lt("e", 32)]), &pow),
    );
    for (rest, op) in [
        ("core::num::<impl u32>::unchecked_add", BinOp::Add),
        ("core::num::<impl i64>::unchecked_sub", BinOp::Sub),
        ("std::num::<impl u64>::unchecked_mul", BinOp::Mul),
    ] {
        let callee = format!("{STAMP}{rest}");
        assert!(
            matches!(
                super::alloc_bounds::overflow_arith_call(&callee),
                Some(super::OverflowCall::Unchecked(o)) if o == op
            ),
            "`{callee}` is core's own UB-on-overflow operation in a graph that stamps core"
        );
        let leaf = callee.rsplit("::").next().unwrap();
        assert_eq!(
            unchecked_vc_count(
                &with_pow_callee(unchecked_func(leaf, Ty::u32(), vec![]), &callee),
                op
            ),
            1,
            "unguarded `{callee}(a, b)` mints exactly one unchecked-overflow row"
        );
    }
    for callee in ["core::num::<impl i32>::abs", "std::num::<impl i8>::abs"] {
        let stamped = format!("{STAMP}{callee}");
        assert!(super::unwrap_panic::is_signed_abs_mint(&stamped), "`{stamped}` mints");
        // trust-clean's subject admission stays authenticated: such a row is never
        // clean-certified.
        assert!(!super::is_signed_abs_call(&stamped), "`{stamped}` is not admitted");
    }
}

/// Only ONE well-formed leading stamp in front of core's EXACT spelling is read past.
#[test]
fn a_malformed_or_misplaced_stamp_is_not_read_past() {
    for callee in [
        // not 16 hex digits
        "__trust_crate@414739228a72f04::core::num::<impl u32>::unchecked_add",
        "__trust_crate@414739228a72f04fz::core::num::<impl u32>::unchecked_add",
        "__trust_crate@zz4739228a72f04f::core::num::<impl u32>::unchecked_add",
        "__trust_crate@::core::num::<impl u32>::unchecked_add",
        // two stamps
        "__trust_crate@414739228a72f04f::__trust_crate@1973d11b2baa21fa::core::num::<impl u32>::unchecked_add",
        // not core's inherent owner
        "__trust_crate@414739228a72f04f::core::num::nonzero::NonZero::<u32>::unchecked_add",
        "__trust_crate@414739228a72f04f::alloc::num::<impl u32>::unchecked_add",
        "__trust_crate@414739228a72f04f::mycore::num::<impl u32>::unchecked_add",
        // a stamp that is not at the front
        "core::num::<impl u32>::__trust_crate@414739228a72f04f::unchecked_add",
    ] {
        assert!(
            super::numeric_panic::int_inherent_minting(callee).is_none(),
            "`{callee}` must not be read as core's spelling"
        );
        assert!(super::alloc_bounds::overflow_arith_call(callee).is_none(), "`{callee}`");
    }
    for callee in [
        "__trust_crate@414739228a72f04f::core::num::<impl u32>::abs",
        "__trust_crate@414739228a72f04f::core::num::wrapping::Wrapping::<i32>::abs",
        "__trust_crate@414739228a72f04f::user::G::<core::num::wrapping::Wrapping<i32>>::abs",
        "__trust_crate@414739228a72f04::core::num::<impl i32>::abs",
    ] {
        assert!(!super::unwrap_panic::is_signed_abs_mint(callee), "`{callee}` mints no row");
    }
}
