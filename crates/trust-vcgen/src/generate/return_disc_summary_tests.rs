use trust_types::UnwindEdge;
use trust_types::{
    AggregateKind, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Rvalue, SourceSpan, Statement, Terminator, Ty, VariantDef, VcKind, VerifiableBody,
    VerifiableFunction,
};

use super::{
    ReturnDiscCases, compute_return_disc_summaries, function_return_disc_summary,
    generate_unwrap_panic_freedom_vcs, unsupported_mir_vcs,
};

const RAT_NEW: &str = "test::Rat::new";
const RESULT_UNWRAP: &str = "core::result::Result::<T, E>::unwrap";

/// `Result<u64, ()>` in the flattened `lower_enum_adt` shape (`Ok` = 0,
/// `Err` = 1) — identical to the unwrap panic-freedom fixtures.
fn std_result_ty() -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        name: "core::result::Result".into(),
        fields: vec![
            ("__tag".into(), Ty::Int { width: 64, signed: true }),
            ("__v0_0".into(), Ty::u64()),
            ("__v1_0".into(), Ty::Unit),
        ],
        variants: vec![
            VariantDef {
                name: "Ok".into(),
                discriminant: 0,
                fields: vec![("0".into(), Ty::u64())],
            },
            VariantDef {
                name: "Err".into(),
                discriminant: 1,
                fields: vec![("0".into(), Ty::Unit)],
            },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

fn i128_ty() -> Ty {
    Ty::Int { width: 128, signed: true }
}

fn ok_agg(payload: i128) -> Statement {
    result_agg(0, payload)
}

fn err_agg() -> Statement {
    result_agg(1, 0)
}

fn result_agg(variant: usize, payload: i128) -> Statement {
    Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "core::result::Result".into(),
                variant,
                active_field: None,
                args: None,
            },
            vec![Operand::Constant(ConstValue::Int(payload))],
        ),
        span: SourceSpan::default(),
    }
}

fn call_term(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.into(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: false,
    }
}

fn ret_block(id: usize) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts: vec![], terminator: Terminator::Return }
}

fn func_of(
    name: &str,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
    return_ty: Ty,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.rsplit("::").next().unwrap_or(name).into(),
        def_path: name.into(),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count, return_ty },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The real `Rat::new` MIR shape:
/// `fn new(n: i128, d: i128) -> Result<..> { if d == 0 { return Err(..) } .. Ok(..) }`
///   bb0: c = Eq(d, 0); SwitchInt(c) -> [0: bb2(Ok arm)], otherwise: bb1(Err arm)
///   bb1: _0 = Err(..); goto bb3        bb2: _0 = Ok(..); goto bb3       bb3: return
fn rat_new_fn() -> VerifiableFunction {
    func_of(
        RAT_NEW,
        vec![
            LocalDecl { index: 0, ty: std_result_ty(), name: None },
            LocalDecl { index: 1, ty: i128_ty(), name: Some("n".into()) },
            LocalDecl { index: 2, ty: i128_ty(), name: Some("d".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("c".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Int(0)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(3)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![err_agg()],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![ok_agg(7)],
                terminator: Terminator::Goto(BlockId(3)),
            },
            ret_block(3),
        ],
        2,
        std_result_ty(),
    )
}

/// A callee that ALWAYS constructs one variant: `fn f() -> .. { Ok(7) }`
/// (or `Err` with `variant = 1`).
fn unconditional_fn(variant: usize) -> VerifiableFunction {
    func_of(
        RAT_NEW,
        vec![LocalDecl { index: 0, ty: std_result_ty(), name: None }],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![result_agg(variant, 7)],
            terminator: Terminator::Return,
        }],
        0,
        std_result_ty(),
    )
}

/// `fn caller(..) { let r = rat_new(1, <d>); r.unwrap() }` — the call-result
/// receiver shape. `d_arg` is the second actual; `arg_count`/locals decide
/// whether the caller has its own `d` parameter.
fn caller_fn(
    d_arg: Operand,
    extra_locals: Vec<LocalDecl>,
    arg_count: usize,
) -> VerifiableFunction {
    let r_local = extra_locals.len() + 1; // after ret + params
    let x_local = r_local + 1;
    let mut locals = vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }];
    locals.extend(extra_locals);
    locals.push(LocalDecl { index: r_local, ty: std_result_ty(), name: Some("r".into()) });
    locals.push(LocalDecl { index: x_local, ty: Ty::u64(), name: Some("x".into()) });
    func_of(
        "test::caller",
        locals,
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: call_term(
                    RAT_NEW,
                    vec![Operand::Constant(ConstValue::Int(1)), d_arg],
                    r_local,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: call_term(
                    RESULT_UNWRAP,
                    vec![Operand::Move(Place::local(r_local))],
                    x_local,
                    2,
                ),
            },
            ret_block(2),
        ],
        arg_count,
        Ty::u64(),
    )
}

fn unverified_row_count(func: &VerifiableFunction) -> usize {
    unsupported_mir_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind.ends_with("::panic-freedom-unverified"))
        })
        .count()
}

fn has_and_conjunct(f: &Formula, pred: &dyn Fn(&Formula) -> bool) -> bool {
    if pred(f) {
        return true;
    }
    match f {
        Formula::And(cs) => cs.iter().any(|c| has_and_conjunct(c, pred)),
        _ => false,
    }
}

fn is_int(f: &Formula, v: i128) -> bool {
    matches!(f, Formula::Int(n) if *n == v)
}

fn base_var_is(f: &Formula, name: &str) -> bool {
    f.var_name().is_some_and(|n| n.split('#').next() == Some(name))
}

/// `ite(<lhs> == 0, 1, 0) == 1` — the instantiated Rat::new tag body, with
/// `lhs_pred` probing the substituted second actual.
fn ite_body_with(f: &Formula, lhs_pred: &dyn Fn(&Formula) -> bool) -> bool {
    let Formula::Eq(l, r) = f else { return false };
    if !is_int(r, 1) {
        return false;
    }
    let Formula::Ite(c, t, e) = l.as_ref() else { return false };
    if !is_int(t, 1) || !is_int(e, 0) {
        return false;
    }
    matches!(c.as_ref(), Formula::Eq(cl, cr) if lhs_pred(cl) && is_int(cr, 0))
}

// ── summary recognizer ──────────────────────────────────────────────────

/// The Rat::new shape yields the GUARD-CONDITIONED summary
/// `tag == ite(d == 0, ERR, OK)` over the callee's own formals.
#[test]
fn rat_new_shape_yields_guard_conditioned_summary() {
    let s = function_return_disc_summary(&rat_new_fn())
        .expect("the Rat::new shape must be summarized");
    assert_eq!(s.enum_name, "core::result::Result");
    assert_eq!(s.params, vec!["n".to_string(), "d".to_string()]);
    let ReturnDiscCases::GuardConditioned { cond, then_tag, else_tag } = &s.cases else {
        panic!("expected the guard-conditioned grade; got {:?}", s.cases);
    };
    assert_eq!((*then_tag, *else_tag), (1, 0), "d == 0 -> Err (1), else Ok (0)");
    assert!(
        matches!(cond, Formula::Eq(l, r) if base_var_is(l, "d") && is_int(r, 0)),
        "cond must be the callee's own `d == 0`: {cond:?}"
    );
}

/// Inverse polarity — `if d != 0 { Ok(..) } else { Err(..) }` (a `Ne`
/// comparison, arms swapped) — is covered: `tag == ite(d != 0, OK, ERR)`.
#[test]
fn inverse_polarity_ne_guard_is_recognized() {
    let mut func = rat_new_fn();
    // c = Ne(d, 0); switch [0: bb1(Err)], otherwise bb2(Ok).
    let Statement::Assign { rvalue, .. } = &mut func.body.blocks[0].stmts[0] else {
        unreachable!()
    };
    *rvalue = Rvalue::BinaryOp(
        BinOp::Ne,
        Operand::Copy(Place::local(2)),
        Operand::Constant(ConstValue::Int(0)),
    );
    let Terminator::SwitchInt { targets, otherwise, .. } = &mut func.body.blocks[0].terminator
    else {
        unreachable!()
    };
    *targets = vec![(0, BlockId(1))];
    *otherwise = BlockId(2);
    let s = function_return_disc_summary(&func).expect("the Ne polarity must be summarized");
    let ReturnDiscCases::GuardConditioned { cond, then_tag, else_tag } = &s.cases else {
        panic!("expected the guard-conditioned grade; got {:?}", s.cases);
    };
    assert_eq!((*then_tag, *else_tag), (0, 1), "d != 0 -> Ok (0), else Err (1)");
    assert!(
        matches!(cond, Formula::Not(inner)
            if matches!(inner.as_ref(), Formula::Eq(l, r) if base_var_is(l, "d") && is_int(r, 0))),
        "cond must be `!(d == 0)`: {cond:?}"
    );
}

/// A callee that always returns one variant yields the UNCONDITIONAL grade.
#[test]
fn unconditional_ok_callee_is_summarized() {
    let s = function_return_disc_summary(&unconditional_fn(0))
        .expect("an always-Ok callee must be summarized");
    assert_eq!(s.cases, ReturnDiscCases::Unconditional { tag: 0 });
    let s = function_return_disc_summary(&unconditional_fn(1))
        .expect("an always-Err callee must be summarized");
    assert_eq!(s.cases, ReturnDiscCases::Unconditional { tag: 1 });
}

/// FAIL-CLOSED: a SECOND branch point on a return arm is outside the
/// straight-line shape — no summary.
#[test]
fn second_branch_point_fails_closed() {
    let mut func = rat_new_fn();
    func.body.blocks[2].terminator = Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(1)),
        targets: vec![(0, BlockId(3))],
        otherwise: BlockId(3),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    assert!(
        function_return_disc_summary(&func).is_none(),
        "a second branch point before the arm's return must fail closed"
    );
    assert!(compute_return_disc_summaries(&[func]).is_empty());
}

/// FAIL-CLOSED: a parameter the guard reads that is WRITTEN in the body is
/// two-valued — the entry condition would not be the branch condition.
#[test]
fn written_guard_param_fails_closed() {
    let mut func = rat_new_fn();
    func.body.blocks[1].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(5))),
            span: SourceSpan::default(),
        },
    );
    assert!(
        function_return_disc_summary(&func).is_none(),
        "a body-written guard parameter must fail closed"
    );
}

/// FAIL-CLOSED: a non-aggregate `_0` write (an opaque whole-value move) is
/// a construction channel the scan cannot pin — no summary.
#[test]
fn non_aggregate_return_write_fails_closed() {
    let mut func = rat_new_fn();
    func.body.blocks[2].stmts[0] = Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    };
    assert!(function_return_disc_summary(&func).is_none());
}

/// FAIL-CLOSED: a non-modeled return type (a user enum named like Result)
/// never summarizes.
#[test]
fn user_enum_return_type_fails_closed() {
    let mut func = rat_new_fn();
    if let Ty::Adt { name, .. } = &mut func.body.locals[0].ty {
        *name = "mycrate::Result".into();
    }
    assert!(function_return_disc_summary(&func).is_none());
}

// ── use site (the unwrap panic-freedom summary-pinned shape) ────────────

fn with_summaries<T>(callees: &[VerifiableFunction], f: impl FnOnce() -> T) -> T {
    let _summary_scope = crate::enter_test_callee_summaries(
        crate::CalleeSummaryContext::default()
            .with_return_disc_summaries(compute_return_disc_summaries(callees)),
    );
    f()
}

/// (1) Const-args receiver `let r = rat_new(1, 2); r.unwrap()`: the VC body
/// is the GROUND `ite(2 == 0, 1, 0) == 1` (UNSAT — proved) and the
/// fail-closed UnsupportedMir row is REPLACED, never doubled.
#[test]
fn const_args_call_receiver_gets_ground_unsat_body() {
    let caller = caller_fn(Operand::Constant(ConstValue::Int(2)), vec![], 0);
    let (vcs, rows) = with_summaries(&[rat_new_fn()], || {
        (generate_unwrap_panic_freedom_vcs(&caller), unverified_row_count(&caller))
    });
    assert_eq!(vcs.len(), 1, "exactly one panic-freedom VC for the one unwrap");
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| ite_body_with(f, &|l| is_int(l, 2))),
        "the body must be the ground `ite(2 == 0, 1, 0) == 1`: {:?}",
        vcs[0].formula
    );
    assert_eq!(rows, 0, "the UnsupportedMir row must be replaced");
}

/// SOUNDNESS polarity: `rat_new(1, 0).unwrap()` — a GENUINE panic — gets
/// the ground SAT body `ite(0 == 0, 1, 0) == 1`; the row can never prove.
#[test]
fn zero_denominator_receiver_stays_sat_shaped() {
    let caller = caller_fn(Operand::Constant(ConstValue::Int(0)), vec![], 0);
    let vcs = with_summaries(&[rat_new_fn()], || generate_unwrap_panic_freedom_vcs(&caller));
    assert_eq!(vcs.len(), 1);
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| ite_body_with(f, &|l| is_int(l, 0))),
        "the body must be the ground-SAT `ite(0 == 0, 1, 0) == 1`: {:?}",
        vcs[0].formula
    );
}

/// (2) Symbolic unguarded `fn caller(d) {{ rat_new(1, d).unwrap() }}`: the
/// VC exists with the SYMBOLIC body `ite(d == 0, 1, 0) == 1` and NO
/// dominating guard — SAT-shaped, the row stays failed (fail-closed).
#[test]
fn symbolic_unguarded_receiver_is_refutable() {
    let caller = caller_fn(
        Operand::Copy(Place::local(1)),
        vec![LocalDecl { index: 1, ty: i128_ty(), name: Some("d".into()) }],
        1,
    );
    let (vcs, rows) = with_summaries(&[rat_new_fn()], || {
        (generate_unwrap_panic_freedom_vcs(&caller), unverified_row_count(&caller))
    });
    assert_eq!(vcs.len(), 1);
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| ite_body_with(f, &|l| base_var_is(l, "d"))),
        "the body must be `ite(d == 0, 1, 0) == 1` over the CALLER's `d`: {:?}",
        vcs[0].formula
    );
    assert_eq!(rows, 0);
}

/// (3) Dominating caller guard `if d != 0 {{ r.unwrap() }}`: the arm's path
/// guard — the bool temp resolved through its def to `!(d == 0)` — is
/// conjoined with the ite body `ite(d == 0, 1, 0) == 1`: the UNSAT shape.
#[test]
fn caller_guarded_symbolic_receiver_gets_unsat_shape() {
    let mut caller = caller_fn(
        Operand::Copy(Place::local(1)),
        vec![LocalDecl { index: 1, ty: i128_ty(), name: Some("d".into()) }],
        1,
    );
    // Rebuild bb1..: c = Eq(d, 0); SwitchInt(c) -> [0: bb2(unwrap)], else bb3.
    caller.body.locals.push(LocalDecl { index: 4, ty: Ty::Bool, name: Some("c".into()) });
    caller.body.blocks[1] = BasicBlock {
        id: BlockId(1),
        stmts: vec![Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(0)),
            ),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::SwitchInt {
            discr: Operand::Move(Place::local(4)),
            targets: vec![(0, BlockId(2))],
            otherwise: BlockId(3),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    };
    caller.body.blocks[2] = BasicBlock {
        id: BlockId(2),
        stmts: vec![],
        terminator: call_term(RESULT_UNWRAP, vec![Operand::Move(Place::local(2))], 3, 4),
    };
    caller.body.blocks.push(ret_block(3));
    caller.body.blocks.push(ret_block(4));
    let (vcs, rows) = with_summaries(&[rat_new_fn()], || {
        (generate_unwrap_panic_freedom_vcs(&caller), unverified_row_count(&caller))
    });
    assert_eq!(vcs.len(), 1);
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| ite_body_with(f, &|l| base_var_is(l, "d"))),
        "the ite body over `d` must be present: {:?}",
        vcs[0].formula
    );
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| guard_negates_d_eq_zero(f)),
        "the dominating `!(d == 0)` arm guard must be conjoined: {:?}",
        vcs[0].formula
    );
    assert_eq!(rows, 0);
}

/// The bb2 arm guard: the switch temp's 0 (false) edge, resolved through
/// the bool def to the negated comparison `!(d == 0)`.
fn guard_negates_d_eq_zero(f: &Formula) -> bool {
    matches!(f, Formula::Not(inner)
        if matches!(inner.as_ref(), Formula::Eq(l, r) if base_var_is(l, "d") && is_int(r, 0)))
}

/// (4) A callee OUTSIDE the recognized shape (second branch point): no
/// summary — the call-result receiver keeps the fail-closed UnsupportedMir
/// row and no solvable VC is emitted.
#[test]
fn unsummarized_callee_falls_back_to_unsupported_row() {
    let mut branchy = rat_new_fn();
    branchy.body.blocks[2].terminator = Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(1)),
        targets: vec![(0, BlockId(3))],
        otherwise: BlockId(3),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let caller = caller_fn(Operand::Constant(ConstValue::Int(2)), vec![], 0);
    let (vcs, rows) = with_summaries(&[branchy], || {
        (generate_unwrap_panic_freedom_vcs(&caller), unverified_row_count(&caller))
    });
    assert!(vcs.is_empty(), "no summary -> no solvable VC");
    assert_eq!(rows, 1, "the fail-closed row must remain");
}

/// (5) Unconditional-Ok callee: the receiver tag is pinned GROUND — the
/// body is the trivially-UNSAT `0 == 1` (proved); the always-Err twin stays
/// SAT-shaped (`1 == 1` — a genuine panic can never prove).
#[test]
fn unconditional_callee_pins_receiver_tag() {
    let caller = caller_fn(Operand::Constant(ConstValue::Int(2)), vec![], 0);
    let vcs =
        with_summaries(&[unconditional_fn(0)], || generate_unwrap_panic_freedom_vcs(&caller));
    assert_eq!(vcs.len(), 1);
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| matches!(f, Formula::Eq(l, r)
            if is_int(l, 0) && is_int(r, 1))),
        "always-Ok callee must yield the ground body `0 == 1`: {:?}",
        vcs[0].formula
    );
    let vcs =
        with_summaries(&[unconditional_fn(1)], || generate_unwrap_panic_freedom_vcs(&caller));
    assert_eq!(vcs.len(), 1);
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| matches!(f, Formula::Eq(l, r)
            if is_int(l, 1) && is_int(r, 1))),
        "always-Err callee must yield the SAT body `1 == 1`: {:?}",
        vcs[0].formula
    );
}

/// SOUNDNESS GATE (S2c staleness): an actual that is REASSIGNED between the
/// call and the unwrap would leave the substituted cond reading the WRONG
/// value — such an actual is refused and the fail-closed row stays.
#[test]
fn reassigned_actual_falls_back() {
    let mut caller = caller_fn(
        Operand::Copy(Place::local(1)),
        vec![LocalDecl { index: 1, ty: i128_ty(), name: Some("d".into()) }],
        1,
    );
    // `d = 5` after the rat_new call: `d` is two-valued across the span.
    caller.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(5))),
        span: SourceSpan::default(),
    });
    let (vcs, rows) = with_summaries(&[rat_new_fn()], || {
        (generate_unwrap_panic_freedom_vcs(&caller), unverified_row_count(&caller))
    });
    assert!(vcs.is_empty(), "a reassigned actual must never be modeled");
    assert_eq!(rows, 1);
}
