use trust_types::UnwindEdge;
use trust_types::{
    AssertMessage, BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VerifiableBody,
    VerifiableFunction,
};

use super::{build_semantic_guard_map, compute_trivial_setter_summaries};
use crate::{SetterSrc, SetterSummary};

const SETTER: &str = "test::set";

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

fn deref_store(ptr_local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign {
        place: Place { local: ptr_local, projections: vec![Projection::Deref] },
        rvalue,
        span: SourceSpan::default(),
    }
}

/// `fn set(p: &mut u32, v: u32) { *p = v; }` — the fixture callee
/// (tests/trust-falsification/proved/assert_mut_setter_identity.rs).
fn setter_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "set".into(),
        def_path: SETTER.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(u32_ty()) },
                    name: Some("p".into()),
                },
                LocalDecl { index: 2, ty: u32_ty(), name: Some("v".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![deref_store(1, Rvalue::Use(Operand::Copy(Place::local(2))))],
                terminator: Terminator::Return,
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

/// The fixture caller: `let mut a = x; set(&mut a, v);` — bb0 assigns
/// `a = x`, materializes `_5 = &mut a`, and calls; bb1 returns.
fn caller_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "test::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: u32_ty(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: u32_ty(), name: Some("v".into()) },
                LocalDecl { index: 3, ty: u32_ty(), name: Some("a".into()) },
                LocalDecl { index: 4, ty: Ty::Unit, name: Some("_4".into()) },
                LocalDecl {
                    index: 5,
                    ty: Ty::Ref { mutable: true, inner: Box::new(u32_ty()) },
                    name: Some("_5".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(3) },
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: SETTER.into(),
                        args: vec![
                            Operand::Move(Place::local(5)),
                            Operand::Copy(Place::local(2)),
                        ],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Guards threaded to the caller's post-call block with the given summary
/// set installed in an unwind-safe test scope.
fn post_call_guards_with(
    funcs: &[VerifiableFunction],
    caller: &VerifiableFunction,
) -> Vec<Formula> {
    let _summary_scope = crate::enter_test_callee_summaries(
        crate::CalleeSummaryContext::default()
            .with_setter_summaries(compute_trivial_setter_summaries(funcs)),
    );
    build_semantic_guard_map(caller).get(&BlockId(1)).cloned().unwrap_or_default()
}

// ---------------- recognizer: positive ----------------

#[test]
fn recognizes_param_source_setter() {
    assert_eq!(
        compute_trivial_setter_summaries(&[setter_fn()]).get(SETTER),
        Some(&SetterSummary {
            param_count: 2,
            ptr_param: 1,
            pointee: (32, false),
            src: SetterSrc::Param(2),
        }),
    );
}

/// The REAL analysis-phase (pre-optimization) MIR of `fn set(p, v) { *p = v }`,
/// which the summaries are computed over (NOT the collapsed optimized form):
///   StorageLive(_3); _3 = copy _2; (*_1) = move _3; StorageDead(_3);
///   _0 = const (); return
/// The recognizer must trace the store source `_3` through the temp copy to the
/// param `_2` and ignore the unit-return assign — else the summary is never
/// minted (the exact stage2 gap: `compute -> 0 setter(s)`, setter fixture red).
#[test]
fn recognizes_analysis_phase_temp_copy_setter() {
    let mut f = setter_fn();
    // local _3: the intermediate temp copy.
    f.body.locals.push(LocalDecl { index: 3, ty: u32_ty(), name: Some("_3".into()) });
    f.body.blocks[0].stmts = vec![
        Statement::StorageLive(3),
        Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
            span: SourceSpan::default(),
        },
        deref_store(1, Rvalue::Use(Operand::Move(Place::local(3)))),
        Statement::StorageDead(3),
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Unit)),
            span: SourceSpan::default(),
        },
    ];
    assert_eq!(
        compute_trivial_setter_summaries(&[f]).get(SETTER),
        Some(&SetterSummary {
            param_count: 2,
            ptr_param: 1,
            pointee: (32, false),
            src: SetterSrc::Param(2),
        }),
        "the analysis-phase temp-copy setter shape must be recognized"
    );
}

/// SOUNDNESS: a COMPUTED store source (`*p = v + 1`, modelled as a temp
/// `_3 = _2` then a second write, or a non-copy temp def) must NOT be
/// recognized — the copy chain only follows pure whole-local copies.
#[test]
fn rejects_computed_temp_source_setter() {
    let mut f = setter_fn();
    f.body.locals.push(LocalDecl { index: 3, ty: u32_ty(), name: Some("_3".into()) });
    f.body.blocks[0].stmts = vec![
        // `_3 = _2 + 1` (a BinaryOp, not a whole-local copy) — reject.
        Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                trust_types::BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Uint(1, 32)),
            ),
            span: SourceSpan::default(),
        },
        deref_store(1, Rvalue::Use(Operand::Move(Place::local(3)))),
    ];
    assert_eq!(
        compute_trivial_setter_summaries(&[f]).get(SETTER),
        None,
        "a computed (non-copy) store source must fail closed"
    );
}

#[test]
fn recognizes_const_source_setter() {
    // `fn set(p: &mut u32) { *p = 7; }` — a goto-chained epilogue block is
    // still one straight entry→return chain.
    let mut f = setter_fn();
    f.body.locals.truncate(2);
    f.body.arg_count = 1;
    f.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![deref_store(1, Rvalue::Use(Operand::Constant(ConstValue::Int(7))))],
            terminator: Terminator::Goto(BlockId(1)),
        },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
    ];
    assert_eq!(
        compute_trivial_setter_summaries(&[f]).get(SETTER),
        Some(&SetterSummary {
            param_count: 1,
            ptr_param: 1,
            pointee: (32, false),
            src: SetterSrc::Const(7),
        }),
    );
}

// ---------------- recognizer: fail-closed negatives ----------------

#[test]
fn rejects_computed_source() {
    // The `bump` mutant shape (`*p = <computed>`): a second value write
    // (the compute) AND a non-parameter source — no summary.
    let mut f = setter_fn();
    f.body.locals.push(LocalDecl { index: 3, ty: u32_ty(), name: Some("_3".into()) });
    f.body.blocks[0].stmts = vec![
        Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                trust_types::BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Int(1)),
            ),
            span: SourceSpan::default(),
        },
        deref_store(1, Rvalue::Use(Operand::Copy(Place::local(3)))),
    ];
    assert!(compute_trivial_setter_summaries(&[f]).is_empty());
}

#[test]
fn rejects_branching_body() {
    // A SwitchInt can bypass the store — no summary, even though the
    // store statement itself is trivial.
    let mut f = setter_fn();
    f.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(0, BlockId(1))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![deref_store(1, Rvalue::Use(Operand::Copy(Place::local(2))))],
            terminator: Terminator::Goto(BlockId(2)),
        },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
    ];
    assert!(compute_trivial_setter_summaries(&[f]).is_empty());
}

#[test]
fn rejects_unreachable_store_block() {
    // The single store sits OFF the entry→return chain: the callee returns
    // WITHOUT storing, so a summary would be FALSE — must fail closed.
    let mut f = setter_fn();
    f.body.blocks = vec![
        BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![deref_store(1, Rvalue::Use(Operand::Copy(Place::local(2))))],
            terminator: Terminator::Return,
        },
    ];
    assert!(compute_trivial_setter_summaries(&[f]).is_empty());
}

#[test]
fn rejects_call_and_assert_terminators() {
    // Any callee/assert in the body (a `wrapping_add` call, an overflow
    // check) — no summary.
    let mut with_call = setter_fn();
    with_call.body.blocks[0].terminator = Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: "other".into(),
        args: vec![],
        dest: Place::local(0),
        target: Some(BlockId(0)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: false,
    };
    assert!(compute_trivial_setter_summaries(&[with_call]).is_empty());

    let mut with_assert = setter_fn();
    with_assert.body.blocks[0].terminator = Terminator::Assert {
        unwind: UnwindEdge::Unreachable,
        cond: Operand::Constant(ConstValue::Bool(true)),
        expected: true,
        msg: AssertMessage::Custom("x".into()),
        target: BlockId(0),
        span: SourceSpan::default(),
    };
    assert!(compute_trivial_setter_summaries(&[with_assert]).is_empty());
}

#[test]
fn rejects_non_mut_ref_raw_ptr_and_whole_store() {
    // Shared-ref param — no summary.
    let mut shared = setter_fn();
    shared.body.locals[1].ty = Ty::Ref { mutable: false, inner: Box::new(u32_ty()) };
    assert!(compute_trivial_setter_summaries(&[shared]).is_empty());

    // Raw-pointer param — no summary.
    let mut raw = setter_fn();
    raw.body.locals[1].ty = Ty::RawPtr { mutable: true, pointee: Box::new(u32_ty()) };
    assert!(compute_trivial_setter_summaries(&[raw]).is_empty());

    // Whole-param store `p = v` (no Deref) — no summary.
    let mut whole = setter_fn();
    whole.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
        span: SourceSpan::default(),
    }];
    assert!(compute_trivial_setter_summaries(&[whole]).is_empty());

    // Projected store `(*p).0 = v` — no summary.
    let mut projected = setter_fn();
    projected.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] },
        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
        span: SourceSpan::default(),
    }];
    assert!(compute_trivial_setter_summaries(&[projected]).is_empty());
}

#[test]
fn rejects_non_param_and_out_of_range_sources() {
    // Source local is NOT a parameter — no summary.
    let mut non_param = setter_fn();
    non_param.body.locals.push(LocalDecl { index: 3, ty: u32_ty(), name: None });
    non_param.body.blocks[0].stmts =
        vec![deref_store(1, Rvalue::Use(Operand::Copy(Place::local(3))))];
    assert!(compute_trivial_setter_summaries(&[non_param]).is_empty());

    // Constant outside the pointee's range (u32 cannot hold -1) — no summary.
    let mut oob = setter_fn();
    oob.body.blocks[0].stmts =
        vec![deref_store(1, Rvalue::Use(Operand::Constant(ConstValue::Int(-1))))];
    assert!(compute_trivial_setter_summaries(&[oob]).is_empty());
}

// ---------------- call-site effect ----------------

#[test]
fn call_site_gets_exact_post_call_fact() {
    let guards = post_call_guards_with(&[setter_fn()], &caller_fn());
    // The target is pinned to the call terminator token (`a#s0_t`) — the
    // SAME token the version oracle gives every post-call read of the
    // mut-borrowed `a` — and the value arg is read at its pre-call value
    // (the bare param `v`).
    let expected = Formula::Eq(
        Box::new(Formula::Var("a#s0_t".into(), Sort::Int)),
        Box::new(Formula::Var("v".into(), Sort::Int)),
    );
    assert!(
        guards.contains(&expected),
        "the setter call site must carry `a#s0_t == v`; got {guards:?}"
    );
}

#[test]
fn no_summary_emits_no_call_site_fact() {
    // Fail-closed at the USE site: no installed summary (the default) ⇒ no
    // fact about the mut-borrow target.
    let guards =
        build_semantic_guard_map(&caller_fn()).get(&BlockId(1)).cloned().unwrap_or_default();
    // `a#s0_t` is the post-call token — the ONLY name a setter fact could
    // pin (the stale pre-call block-def `a#s0_0 == x` is expected and inert).
    assert!(
        guards.iter().all(|f| !format!("{f:?}").contains("a#s0_t")),
        "an unsummarized callee must yield NO target fact; got {guards:?}"
    );
}

#[test]
fn reseated_borrow_temp_emits_no_fact() {
    // A second whole-local def of the borrow temp makes the pointer
    // ambiguous — the call site must fail closed.
    let mut caller = caller_fn();
    caller.body.locals.push(LocalDecl { index: 6, ty: u32_ty(), name: Some("b".into()) });
    caller.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(6) },
        span: SourceSpan::default(),
    });
    let guards = post_call_guards_with(&[setter_fn()], &caller);
    assert!(
        guards.iter().all(|f| {
            let s = format!("{f:?}");
            !s.contains("a#s0_t") && !s.contains("b#s0_t")
        }),
        "a reseatable borrow temp must yield NO target fact; got {guards:?}"
    );
}

#[test]
fn arity_mismatch_emits_no_fact() {
    // Same callee name reached with the WRONG arity — fail closed.
    let mut caller = caller_fn();
    let Terminator::Call { args, .. } = &mut caller.body.blocks[0].terminator else {
        unreachable!()
    };
    args.push(Operand::Constant(ConstValue::Int(0)));
    let guards = post_call_guards_with(&[setter_fn()], &caller);
    assert!(
        guards.iter().all(|f| !format!("{f:?}").contains("a#s0_t")),
        "an arity-mismatched call must yield NO target fact; got {guards:?}"
    );
}

#[test]
fn target_type_mismatch_emits_no_fact() {
    // The caller's borrow target is declared u64 but the summary's pointee
    // is u32 (a homonym/collision defense) — fail closed.
    let mut caller = caller_fn();
    caller.body.locals[3].ty = Ty::Int { width: 64, signed: false };
    let guards = post_call_guards_with(&[setter_fn()], &caller);
    assert!(
        guards.iter().all(|f| !format!("{f:?}").contains("a#s0_t")),
        "a pointee-type mismatch must yield NO target fact; got {guards:?}"
    );
}

#[test]
fn const_source_setter_pins_target_to_const() {
    // `fn set7(p: &mut u32) { *p = 7; }` called as `set7(&mut a)`.
    let mut setter = setter_fn();
    setter.body.locals.truncate(2);
    setter.body.arg_count = 1;
    setter.body.blocks[0].stmts =
        vec![deref_store(1, Rvalue::Use(Operand::Constant(ConstValue::Int(7))))];
    let mut caller = caller_fn();
    let Terminator::Call { args, .. } = &mut caller.body.blocks[0].terminator else {
        unreachable!()
    };
    *args = vec![Operand::Move(Place::local(5))];
    let guards = post_call_guards_with(&[setter], &caller);
    let expected = Formula::Eq(
        Box::new(Formula::Var("a#s0_t".into(), Sort::Int)),
        Box::new(Formula::Int(7)),
    );
    assert!(
        guards.contains(&expected),
        "the const-setter call site must carry `a#s0_t == 7`; got {guards:?}"
    );
}
