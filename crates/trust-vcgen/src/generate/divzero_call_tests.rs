use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Sort, SourceSpan,
    Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

use super::generate_vcs;

/// Number of div/rem-by-zero obligations the pipeline emits for `func`.
fn divzero_vc_count(func: &VerifiableFunction) -> usize {
    generate_vcs(func)
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::DivisionByZero | VcKind::RemainderByZero))
        .count()
}

/// True if the rendered formula mentions `name` — confirms a conjoined guard /
/// precondition reaches the VC formula (so the solver discharges it) without
/// running an SMT solver in the unit test.
fn formula_mentions_var(f: &Formula, name: &str) -> bool {
    f.to_smtlib().contains(name)
}

/// `fn(a: ty, b: ty) -> ty { a.OP(b) }` as a single-block tail call. The
/// receiver `a` lowers to MIR arg 0 (local 1), the divisor `b` to arg 1
/// (local 2) — exactly the shape the recognizer keys on. `divisor` lets a
/// caller override arg 1 with a constant. `pre` optionally adds a precondition.
fn method_div_func(
    method: &str,
    ty: Ty,
    divisor: Operand,
    pre: Vec<Formula>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "div_caller".to_string(),
        def_path: "test::div_caller".to_string(),
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
                    func: format!("core::num::<impl i32>::{method}"),
                    args: vec![Operand::Copy(Place::local(1)), divisor],
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

/// `iter.step_by(n)` — the iterator receiver is arg 0 (local 1), the step `n`
/// is arg 1 (local 2). `n == 0` panics in the stdlib.
fn step_by_func(step: Operand) -> VerifiableFunction {
    VerifiableFunction {
        name: "step_caller".to_string(),
        def_path: "test::step_caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("iter".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "core::iter::traits::iterator::Iterator::step_by".to_string(),
                    args: vec![Operand::Copy(Place::local(1)), step],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                },
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ----- fire on bug: unguarded dynamic divisor -----

#[test]
fn flags_unguarded_div_euclid() {
    // `a.div_euclid(b)` with `b` an unbounded i32 param PANICS when `b == 0`,
    // but lowers to a Call with no BinaryOp — it was reported vacuously safe.
    // It must now produce a DivisionByZero obligation.
    let func = method_div_func("div_euclid", Ty::i32(), Operand::Copy(Place::local(2)), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "unguarded `a.div_euclid(b)` must emit a DivisionByZero obligation"
    );
}

#[test]
fn flags_unguarded_rem_euclid() {
    // `a.rem_euclid(b)` panics on a zero divisor — RemainderByZero obligation.
    let func = method_div_func("rem_euclid", Ty::i32(), Operand::Copy(Place::local(2)), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::RemainderByZero)),
        "unguarded `a.rem_euclid(b)` must emit a RemainderByZero obligation"
    );
}

#[test]
fn checked_div_is_total_no_obligation() {
    // `a.checked_div(b)` returns `None` on a zero divisor — it NEVER panics, so
    // it must emit NO DivisionByZero obligation even when the divisor is a fully
    // unconstrained runtime value. (Regression pin for the false refutation of
    // `n.checked_div(&x).unwrap_or_else(BigUint::zero)`, which is panic-free.)
    let func =
        method_div_func("checked_div", Ty::u32(), Operand::Copy(Place::local(2)), vec![]);
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "`a.checked_div(b)` is total (returns None on zero) and must emit no obligation"
    );
}

#[test]
fn flags_unguarded_div_ceil() {
    // `a.div_ceil(b)` PANICS on `b == 0` exactly like `a / b`, but lowers to a
    // Call with no BinaryOp — it was reported vacuously safe (false-accept).
    // It must now emit a DivisionByZero obligation.
    let func = method_div_func("div_ceil", Ty::u32(), Operand::Copy(Place::local(2)), vec![]);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "unguarded `a.div_ceil(b)` must emit a DivisionByZero obligation"
    );
}

#[test]
fn allows_const_nonzero_div_ceil() {
    // `a.div_ceil(4)` — literal nonzero divisor is provably safe; no obligation
    // (drop-in: a guarded/const `div_ceil` still compiles).
    let func = method_div_func(
        "div_ceil",
        Ty::u32(),
        Operand::Constant(ConstValue::Uint(4, 32)),
        vec![],
    );
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "`a.div_ceil(4)` has a provably-nonzero divisor and must emit no obligation"
    );
}

#[test]
fn checked_rem_is_total_no_obligation() {
    // `a.checked_rem(b)` returns `None` on a zero divisor — it NEVER panics, so
    // it must emit NO RemainderByZero obligation. Total twin of `checked_div`.
    let func =
        method_div_func("checked_rem", Ty::u32(), Operand::Copy(Place::local(2)), vec![]);
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "`a.checked_rem(b)` is total (returns None on zero) and must emit no obligation"
    );
}

#[test]
fn flags_unguarded_step_by() {
    // `iter.step_by(n)` panics when `n == 0`; an unbounded `n` must flag.
    let func = step_by_func(Operand::Copy(Place::local(2)));
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "unguarded `iter.step_by(n)` must emit a non-zero (DivisionByZero) obligation"
    );
}

// ----- no false positive: trivially-safe / unrelated calls -----

#[test]
fn allows_const_nonzero_div_euclid() {
    // `a.div_euclid(4)` — a literal nonzero divisor is trivially proved safe;
    // no obligation at all (mirrors the BinaryOp const-nonzero skip).
    let func =
        method_div_func("div_euclid", Ty::i32(), Operand::Constant(ConstValue::Int(4)), vec![]);
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "`a.div_euclid(4)` has a provably-nonzero divisor and must emit no obligation"
    );
}

#[test]
fn allows_const_nonzero_step_by() {
    let func = step_by_func(Operand::Constant(ConstValue::Uint(2, 64)));
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "`iter.step_by(2)` has a provably-nonzero step and must emit no obligation"
    );
}

#[test]
fn ignores_ordinary_call() {
    // An ordinary (non-division) method call must not produce any div-by-zero
    // obligation — the recognizer must not broadly fail-close on every Call.
    let func =
        method_div_func("wrapping_add", Ty::i32(), Operand::Copy(Place::local(2)), vec![]);
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "a non-division call must not produce a div-by-zero obligation"
    );
}

#[test]
fn ignores_float_div_euclid() {
    // `f64::div_euclid(0.0)` does NOT panic (returns inf/nan), so a float
    // divisor must not be flagged — flagging it would false-FAIL ordinary code.
    let func = method_div_func(
        "div_euclid",
        Ty::Float { width: 64 },
        Operand::Copy(Place::local(2)),
        vec![],
    );
    assert_eq!(
        divzero_vc_count(&func),
        0,
        "float `div_euclid` does not panic on a zero divisor and must not be flagged"
    );
}

// ----- guarded: obligation generated but discharged by the conjoined guard -----

#[test]
fn precondition_b_nonzero_carries_into_div_euclid_vc() {
    // `#[requires(b != 0)] a.div_euclid(b)` is safe. The obligation IS
    // generated, but its formula must carry the precondition `b != 0` so the
    // solver discharges it — the safe/buggy distinction without an SMT run.
    let pre = Formula::Not(Box::new(Formula::Eq(
        Box::new(Formula::Var("b".into(), Sort::Int)),
        Box::new(Formula::Int(0)),
    )));
    let func =
        method_div_func("div_euclid", Ty::i32(), Operand::Copy(Place::local(2)), vec![pre]);
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("guarded div_euclid still generates the obligation (discharged at solve time)");
    assert!(
        formula_mentions_var(&vc.formula, "b"),
        "the div_euclid VC must reference the divisor `b` so the precondition \
         `b != 0` can discharge it; formula: {:?}",
        vc.formula
    );
}

#[test]
fn dominating_nonzero_guard_carries_into_div_euclid_vc() {
    // `if b != 0 { a.div_euclid(b) }` lowered to MIR: block 0 switches on the
    // divisor `b`; the `b == 0` edge skips the call (block 2), the `otherwise`
    // (`b != 0`) edge reaches the call block (block 1). The path-guard map must
    // conjoin `b != 0` onto the call's div-by-zero VC so the solver discharges
    // it — an unguarded call (the `flags_*` tests) has no such guard and fails.
    let func = VerifiableFunction {
        name: "guarded_div".to_string(),
        def_path: "test::guarded_div".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![
                // block 0: `switch b { 0 => bb2 (skip), _ => bb1 (call) }`.
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        exhaustive_enum_unreachable: false,
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                // block 1: reached only when `b != 0` — `a.div_euclid(b)`.
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::num::<impl i32>::div_euclid".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                // block 2: join / return.
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("guarded div_euclid still generates the obligation (discharged at solve time)");
    // The dominating `b != 0` SwitchInt guard must be conjoined into the VC so
    // the solver proves the failure (`b == 0`) UNSAT on this path.
    assert!(
        formula_mentions_var(&vc.formula, "b"),
        "the dominating `b != 0` guard must reach the div_euclid VC; formula: {:?}",
        vc.formula
    );
}
