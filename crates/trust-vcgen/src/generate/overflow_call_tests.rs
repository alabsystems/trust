use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Sort,
    SourceSpan, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

use super::generate_vcs;

fn overflow_vc_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::ArithmeticOverflow { .. }))
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
                    is_foreign: false,
                },
            }],
            arg_count: 1,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: pre,
        postconditions: vec![],
        spec: Default::default(),
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
                    is_foreign: false,
                },
            }],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: pre,
        postconditions: vec![],
        spec: Default::default(),
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
        vcs.iter()
            .any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })),
        "unguarded `unchecked_add(a, b)` must emit an Add ArithmeticOverflow obligation"
    );
}

#[test]
fn flags_unchecked_sub() {
    let func = unchecked_func("unchecked_sub", Ty::u32(), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter()
            .any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. })),
        "unguarded `unchecked_sub(a, b)` must emit a Sub ArithmeticOverflow obligation"
    );
}

#[test]
fn flags_unchecked_mul() {
    let func = unchecked_func("unchecked_mul", Ty::u32(), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter()
            .any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. })),
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
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
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
