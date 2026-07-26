use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{
    build_semantic_guard_map, compute_return_bound_summaries,
    compute_return_const_set_summaries, compute_return_lower_bound_summaries,
};

const SMALL_DEN: &str = "test::small_den";

fn assign_const(local: usize, v: u128) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(v, 64))),
        span: SourceSpan::default(),
    }
}

/// ny's `small_den` shape: `match g { 0 => 1, 1 => 2, _ => 4 }` — a
/// `SwitchInt` over three arms, each assigning a constant to the return
/// local `_0`, joining at a single `Return`. With `third_arm_const: false`,
/// the otherwise-arm returns `g` instead (`_0 = copy _1`) — ONE non-const
/// return site, which must fail the whole summary closed.
fn small_den_fn(third_arm_const: bool) -> VerifiableFunction {
    let bb3_stmt = if third_arm_const {
        assign_const(0, 4)
    } else {
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        }
    };
    VerifiableFunction {
        name: "small_den".into(),
        def_path: SMALL_DEN.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("g".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign_const(0, 1)],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign_const(0, 2)],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![bb3_stmt],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `fn caller(g) { d = small_den(g); }` — one call, one successor block.
fn caller_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "caller".into(),
        def_path: "test::caller".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("g".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("d".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: SMALL_DEN.into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn small_den_summaries_capture_min_max_and_const_set() {
    let funcs = [small_den_fn(true)];
    assert_eq!(
        compute_return_lower_bound_summaries(&funcs).get(SMALL_DEN),
        Some(&1),
        "every return site is a const >= 1 — the lower summary must be its min"
    );
    assert_eq!(
        compute_return_bound_summaries(&funcs).get(SMALL_DEN),
        Some(&4),
        "every return site is a const <= 4 — the upper summary must be its max"
    );
    assert_eq!(
        compute_return_const_set_summaries(&funcs).get(SMALL_DEN),
        Some(&vec![1, 2, 4]),
        "all-const return sites must yield the exact sorted const set"
    );
}

#[test]
fn one_non_const_return_site_fails_all_summaries_closed() {
    // The otherwise-arm returns `g` — its value is unknown, so NO summary
    // (lower, upper, or set) may be recorded: the bound must hold for
    // EVERY input and EVERY return path.
    let funcs = [small_den_fn(false)];
    assert!(
        compute_return_lower_bound_summaries(&funcs).is_empty(),
        "a non-const return site must fail the lower summary closed"
    );
    assert!(
        compute_return_bound_summaries(&funcs).is_empty(),
        "a non-const return site must fail the upper summary closed"
    );
    assert!(
        compute_return_const_set_summaries(&funcs).is_empty(),
        "a non-const return site must fail the const-set summary closed"
    );
}

#[test]
fn call_defined_return_site_fails_closed() {
    // Replace the otherwise-arm with a RECURSIVE return site
    // `_0 = small_den(g)` — a call dest the const scan cannot see through.
    // Fail-closed: no summary of any shape.
    let mut func = small_den_fn(true);
    func.body.blocks[3] = BasicBlock {
        id: BlockId(3),
        stmts: vec![],
        terminator: Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            func: SMALL_DEN.into(),
            args: vec![Operand::Copy(Place::local(1))],
            dest: Place::local(0),
            target: Some(BlockId(4)),
            span: SourceSpan::default(),
            atomic: None,
            is_unsafe_sig: false,
            is_foreign: false,
        },
    };
    let funcs = [func];
    assert!(
        compute_return_lower_bound_summaries(&funcs).is_empty()
            && compute_return_bound_summaries(&funcs).is_empty()
            && compute_return_const_set_summaries(&funcs).is_empty(),
        "a call-defined (recursive) return site must fail every summary closed"
    );
}

#[test]
fn call_site_gets_lower_upper_and_const_set_facts() {
    let funcs = [small_den_fn(true)];
    let _summary_scope = crate::enter_test_callee_summaries(
        crate::CalleeSummaryContext::default()
            .with_return_bounds(compute_return_bound_summaries(&funcs))
            .with_return_lower_bounds(compute_return_lower_bound_summaries(&funcs))
            .with_return_const_sets(compute_return_const_set_summaries(&funcs)),
    );
    let guards =
        build_semantic_guard_map(&caller_fn()).get(&BlockId(1)).cloned().unwrap_or_default();

    // The dest fact is versioned to the call terminator token (`d#s0_t`),
    // mirroring the stdlib min/max bound emission.
    let d = || Box::new(Formula::Var("d#s0_t".into(), Sort::Int));
    let lower = Formula::Ge(d(), Box::new(Formula::Int(1)));
    let upper = Formula::Le(d(), Box::new(Formula::Int(4)));
    let const_set = Formula::Or(vec![
        Formula::Eq(d(), Box::new(Formula::Int(1))),
        Formula::Eq(d(), Box::new(Formula::Int(2))),
        Formula::Eq(d(), Box::new(Formula::Int(4))),
    ]);
    assert!(
        guards.contains(&lower),
        "call site must carry the summary lower bound `d >= 1`; got {guards:?}"
    );
    assert!(
        guards.contains(&upper),
        "call site must carry the summary upper bound `d <= 4`; got {guards:?}"
    );
    assert!(
        guards.contains(&const_set),
        "call site must carry the exact const-set disjunction; got {guards:?}"
    );
}

#[test]
fn no_summary_emits_no_call_site_fact() {
    // Fail-closed at the USE site too: with no installed summary for the
    // callee (the default), the call dest gets no return-summary fact.
    let guards =
        build_semantic_guard_map(&caller_fn()).get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        guards.iter().all(|f| !format!("{f:?}").contains("d#")),
        "an unsummarized callee must yield NO dest fact; got {guards:?}"
    );
}
