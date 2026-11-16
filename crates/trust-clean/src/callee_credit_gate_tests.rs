//! CALLEE CREDIT: regression pins for `whole_program::first_unresolved_effect`.
//!
//! Both certification gates in `whole_program` claim whole-body panic-freedom plus
//! assumption authority for every caller: `certify_callee_summary` (the summary
//! tier) and `verify_call_graph` (the graph tier). Both read only
//! `trust_vcgen::generate_vcs(func)`. That row set is per-function, so it holds
//! nothing for the code a `Call` or `TailCall` runs, or for the drop glue a
//! `Drop` runs. A panic there is the callee's obligation. A gate that never
//! checks the callee therefore credits the panic to nobody.
//!
//! Every refused probe raises no L0 row and has an `ensures` that holds on its own:
//! `result >= 0` over a `u64` return, or `true`. What decides each verdict is
//! therefore the call, tail call or drop alone. Measured on 521477a0d2, this file
//! run against that commit's unfixed gates:
//!
//! ```text
//! summary tier (proved, assumable)
//!   keyed call to a panicking callee   (true, true)    <- the reported defect
//!   keyed tail call                    (true, true)
//!   drop of a local                    (true, true)
//!   keyless call, keyless tail call    (false, false)  refused since 68160b1461
//! graph tier (Certified)
//!   keyless call or tail call to an in-graph callee the graph refused   true
//!   keyless call that does not establish a certified callee's
//!     `requires` (overflows inside the callee at a = i32::MAX)          true
//!   keyed tail call outside the graph                                   true
//!   drop of a local                                                      true
//! ```
//!
//! A keyed CALL outside the graph was already refused there, by the dominance-scope
//! gate, which admits keyless calls only.
//!
//! The positive controls pin that the gates still certify what they resolve: the
//! same body without the call, a call whose `requires` the caller establishes,
//! and a call or tail call to a callee the graph certified.

#![cfg(test)]

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, CalleeKey, ConstValue, Formula, LocalDecl, Operand,
    Place, ProofLevel, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind,
    VerifiableBody, VerifiableFunction,
};

use crate::composition_transfer::{ProofStatus, ProofStatusRegistry};
use crate::whole_program::{certify_callee_summary, verify_call_graph};

const PANICKING: &str = "probe::always_panics";

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn i32_ty() -> Ty {
    Ty::Int { width: 32, signed: true }
}

/// The key today's extractor mints for a user crate's item: no sysroot tag.
fn user_key() -> CalleeKey {
    CalleeKey {
        sysroot_item: None,
        krate_is_real_sysroot: false,
        krate_name_is_ambiguous: false,
        stable_crate_id: 3,
        krate_name: "probe".into(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    }
}

fn ret_ge_zero() -> Formula {
    Formula::Ge(Box::new(Formula::Var("_0".into(), Sort::Int)), Box::new(Formula::Int(0)))
}

fn one_arg_fn(
    def_path: &str,
    ty: Ty,
    extra_locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: ty.clone(), name: Some("_0".into()) },
        LocalDecl { index: 1, ty: ty.clone(), name: Some("h".into()) },
    ];
    locals.extend(extra_locals);
    VerifiableFunction {
        name: def_path.rsplit("::").next().unwrap_or(def_path).into(),
        def_path: def_path.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![ret_ge_zero()],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn call_h(callee: &str, key: Option<CalleeKey>) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args: vec![Operand::Copy(Place::local(1))],
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: key,
        is_foreign: false,
        unwind: UnwindEdge::Unreachable,
    }
}

/// `fn name(h) -> ty { callee(h) }`: one direct call, its result returned.
fn caller_via_call(
    def_path: &str,
    callee: &str,
    key: Option<CalleeKey>,
    ty: Ty,
) -> VerifiableFunction {
    one_arg_fn(
        def_path,
        ty,
        vec![],
        vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: call_h(callee, key) },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
    )
}

/// `fn name(h: u64) -> u64 { become callee(h) }`.
fn caller_via_tail_call(
    def_path: &str,
    callee: &str,
    key: Option<CalleeKey>,
) -> VerifiableFunction {
    one_arg_fn(
        def_path,
        u64_ty(),
        vec![],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::TailCall {
                func: callee.into(),
                args: vec![Operand::Copy(Place::local(1))],
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: key,
            },
        }],
    )
}

/// `fn drop_only(h: u64, x: PanicsOnDrop) -> u64 { 0 }`: `x` is dropped on the way
/// out, and a user `Drop` impl can panic.
fn drop_only() -> VerifiableFunction {
    let mut f = one_arg_fn(
        "probe::drop_only",
        u64_ty(),
        vec![LocalDecl {
            index: 2,
            ty: Ty::adt("probe::PanicsOnDrop", vec![]),
            name: Some("x".into()),
        }],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Drop {
                    place: Place::local(2),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Unreachable,
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
    );
    f.body.arg_count = 2;
    f
}

/// `fn always_panics(h: u64) -> u64 { u64::MAX + 1 }` in rustc's checked-debug
/// shape: the overflow assert fails on every execution.
fn always_panics() -> VerifiableFunction {
    one_arg_fn(
        PANICKING,
        u64_ty(),
        vec![LocalDecl {
            index: 2,
            ty: Ty::Tuple(vec![u64_ty(), Ty::Bool]),
            name: Some("_2".into()),
        }],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Constant(ConstValue::Uint(u128::from(u64::MAX), 64)),
                        Operand::Constant(ConstValue::Uint(1, 64)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::field(2, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Add),
                    target: BlockId(1),
                    unwind: UnwindEdge::Unreachable,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::field(2, 0))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ],
    )
}

/// `#[requires(x < 100)] #[ensures(result <= 100)] fn bump(x: i32) -> i32 { x + 1 }`
/// (checked). It certifies on its own, and it overflows at `x = i32::MAX`, which
/// only its `requires` rules out.
fn bump() -> VerifiableFunction {
    let mut f = one_arg_fn(
        "probe::bump",
        i32_ty(),
        vec![LocalDecl {
            index: 2,
            ty: Ty::Tuple(vec![i32_ty(), Ty::Bool]),
            name: Some("_2".into()),
        }],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(1)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::field(2, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Add),
                    target: BlockId(1),
                    unwind: UnwindEdge::Unreachable,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::field(2, 0))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ],
    );
    f.body.locals[1].name = Some("x".into());
    f.preconditions = vec![Formula::Lt(
        Box::new(Formula::Var("x".into(), Sort::Int)),
        Box::new(Formula::Int(100)),
    )];
    f.postconditions = vec![Formula::Le(
        Box::new(Formula::Var("_0".into(), Sort::Int)),
        Box::new(Formula::Int(100)),
    )];
    f
}

/// `fn any_arg(a: i32) -> i32 { bump(a) }` with a vacuous `ensures true`, so the
/// verdict turns on the call alone. Keyless, so the graph tier's dominance-scope
/// gate admits it.
fn bump_caller(def_path: &str, requires_a_below_100: bool) -> VerifiableFunction {
    let mut f = caller_via_call(def_path, "probe::bump", None, i32_ty());
    f.body.locals[1].name = Some("a".into());
    f.postconditions = vec![Formula::Bool(true)];
    if requires_a_below_100 {
        f.preconditions = vec![Formula::Lt(
            Box::new(Formula::Var("a".into(), Sort::Int)),
            Box::new(Formula::Int(100)),
        )];
    }
    f
}

/// `fn leaf(h: u64) -> u64 { 7 }`: certifies with no call in it.
fn certified_leaf() -> VerifiableFunction {
    one_arg_fn(
        "probe::leaf",
        u64_ty(),
        vec![],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

/// `(proved, assumable)` at the summary tier.
fn summary_authority(f: &VerifiableFunction) -> (bool, bool) {
    let mut registry = ProofStatusRegistry::new();
    let summary = certify_callee_summary(f, trust_ir::FuncId::new(0), &mut registry);
    (summary.ir_summary.proved, registry.is_assumable(&f.def_path))
}

fn l0_rows(f: &VerifiableFunction) -> Vec<VcKind> {
    trust_vcgen::generate_vcs(f)
        .into_iter()
        .filter(|vc| vc.kind.proof_level() == ProofLevel::L0Safety)
        .map(|vc| vc.kind)
        .collect()
}

/// Whether every postcondition row of `f` refutes (and there is at least one).
fn postcondition_refutes(f: &VerifiableFunction) -> bool {
    let posts: Vec<_> = trust_vcgen::generate_vcs(f)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect();
    !posts.is_empty()
        && posts.iter().all(|vc| {
            matches!(
                crate::vc_refute::check_refute_vc(&crate::prove::augment_with_type_bounds_pub(
                    &vc.formula,
                    f
                )),
                Some(crate::RefuteOutcome::RefutedModulo3)
            )
        })
}

/// The probe's own rows cannot decide its verdict: no L0 row, and a postcondition
/// that refutes. Only the call, tail call or drop is left to decide it.
fn assert_isolated(name: &str, f: &VerifiableFunction) {
    assert_eq!(l0_rows(f), Vec::<VcKind>::new(), "{name}: the probe must raise no L0 row");
    assert!(postcondition_refutes(f), "{name}: the probe's postcondition must refute on its own");
}

fn graph_verdict(program: &[VerifiableFunction], def_path: &str) -> (bool, Option<String>) {
    let result = verify_call_graph(program);
    let verdict = result
        .verdict(def_path)
        .unwrap_or_else(|| panic!("no verdict for {def_path}: {:?}", result.verdicts));
    (verdict.status == ProofStatus::Certified, verdict.open_reason.clone())
}

/// Whether `reason` is the callee-credit clause's refusal and names `what`.
fn refused_by_callee_credit(reason: &Option<String>, what: &str) -> bool {
    reason.as_deref().is_some_and(|r| {
        r.contains(what)
            && r.contains("whole-body panic-freedom is not established at the certification tier")
    })
}

/// THE REPORTED DEFECT: a KEYED call to a user callee that panics. The key is what
/// today's extractor mints for a user item (no sysroot tag). The callee panics on
/// every execution, and the graph tier refuses it on its own overflow row. At the
/// summary tier its caller read `(proved, assumable) = (true, true)`.
#[test]
fn summary_tier_refuses_a_keyed_call_to_a_panicking_callee() {
    let callee = always_panics();
    assert!(
        l0_rows(&callee).iter().any(|k| matches!(k, VcKind::ArithmeticOverflow { .. })),
        "the callee must carry its own overflow row: {:?}",
        l0_rows(&callee)
    );
    assert_eq!(
        summary_authority(&callee),
        (false, false),
        "the callee panics and must not certify"
    );

    let caller = caller_via_call("probe::leaf_only", PANICKING, Some(user_key()), u64_ty());
    assert_isolated("keyed leaf-only caller", &caller);
    assert_eq!(
        summary_authority(&caller),
        (false, false),
        "a body whose only call is a keyed call to a panicking callee must not be \
         certified: a key identifies the callee, it does not certify it"
    );

    // THE CONTROL: the identical body with the call replaced by `_0 = h` certifies,
    // so the call is the only thing the refusal above turns on.
    let mut no_call = caller.clone();
    no_call.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    });
    no_call.body.blocks[0].terminator = Terminator::Goto(BlockId(1));
    assert_eq!(
        summary_authority(&no_call),
        (true, true),
        "the call-free twin must still certify, or the gate is refusing everything"
    );
}

/// Every shape through which a body runs code the summary tier never examined.
/// Before the fix each one read `(true, true)`. The whole table is compared at
/// once, so a regression names every shape that re-opened.
#[test]
fn summary_tier_refuses_every_unresolved_call_tail_call_and_drop() {
    let probes = [
        ("keyed call", caller_via_call("probe::a", PANICKING, Some(user_key()), u64_ty())),
        ("keyless call", caller_via_call("probe::b", PANICKING, None, u64_ty())),
        ("keyed tail call", caller_via_tail_call("probe::c", PANICKING, Some(user_key()))),
        ("keyless tail call", caller_via_tail_call("probe::d", PANICKING, None)),
        ("drop", drop_only()),
    ];
    for (name, f) in &probes {
        assert_isolated(name, f);
    }
    let observed: Vec<_> = probes.iter().map(|(name, f)| (*name, summary_authority(f))).collect();
    let expected: Vec<_> = probes.iter().map(|(name, _)| (*name, (false, false))).collect();
    assert_eq!(
        observed, expected,
        "(proved, assumable): the summary tier resolves no callee and certifies no drop glue"
    );
}

/// Every shape through which a body runs code the graph tier did not certify for
/// that call site. Before the fix each caller was `Certified`. The whole table is
/// compared at once, and each refusal must come from the callee-credit clause and
/// name what it refused.
#[test]
fn graph_tier_refuses_every_unresolved_call_tail_call_and_drop() {
    // Premises: the in-graph panicking callee is refused, `bump` is certified.
    let (callee_certified, reason) = graph_verdict(&[always_panics()], PANICKING);
    assert!(!callee_certified, "the panicking callee must be refused: {reason:?}");
    let (bump_certified, reason) = graph_verdict(&[bump()], "probe::bump");
    assert!(bump_certified, "bump must certify under its own requires: {reason:?}");

    let cases: [(&str, Vec<VerifiableFunction>, &str, &str); 5] = [
        (
            "call to an in-graph callee this graph refused",
            vec![caller_via_call("probe::leaf_only", PANICKING, None, u64_ty()), always_panics()],
            "probe::leaf_only",
            PANICKING,
        ),
        (
            "tail call to an in-graph callee this graph refused",
            vec![caller_via_tail_call("probe::tail_only", PANICKING, None), always_panics()],
            "probe::tail_only",
            PANICKING,
        ),
        (
            "keyed tail call outside the graph",
            vec![caller_via_tail_call("probe::keyed_tail", PANICKING, Some(user_key()))],
            "probe::keyed_tail",
            PANICKING,
        ),
        (
            "call that does not establish a certified callee's requires",
            vec![bump(), bump_caller("probe::any_arg", false)],
            "probe::any_arg",
            "probe::bump",
        ),
        ("drop", vec![drop_only()], "probe::drop_only", "the drop of local _2"),
    ];
    for (name, program, caller, _) in &cases {
        let f = program.iter().find(|f| f.def_path == *caller).expect("caller in program");
        assert_eq!(l0_rows(f), Vec::<VcKind>::new(), "{name}: the caller must raise no L0 row");
    }
    let observed: Vec<_> = cases
        .iter()
        .map(|(name, program, caller, what)| {
            let (certified, reason) = graph_verdict(program, caller);
            (*name, certified, refused_by_callee_credit(&reason, what))
        })
        .collect();
    let expected: Vec<_> = cases.iter().map(|(name, ..)| (*name, false, true)).collect();
    assert_eq!(
        observed, expected,
        "(certified, refused by the callee-credit clause naming the callee or drop)"
    );
}

/// THE POSITIVE CONTROLS for resolution itself: a call and a tail call to a callee
/// the graph certified, and a call whose `requires` the caller establishes, still
/// certify. Without these, every refusal above would also hold of a gate that
/// refuses everything with a call in it.
#[test]
fn graph_tier_still_certifies_what_it_resolved() {
    let leaf = certified_leaf();
    for caller in [
        caller_via_call("probe::via_call", "probe::leaf", None, u64_ty()),
        caller_via_tail_call("probe::via_tail", "probe::leaf", None),
    ] {
        let program = [caller.clone(), leaf.clone()];
        let (leaf_certified, reason) = graph_verdict(&program, "probe::leaf");
        assert!(leaf_certified, "the leaf must certify: {reason:?}");
        let (certified, reason) = graph_verdict(&program, &caller.def_path);
        assert!(
            certified,
            "{}: a call to a certified leaf must certify: {reason:?}",
            caller.def_path
        );
    }
    // The twin of the unestablished-requires case: `a < 100` establishes bump's
    // `x < 100`, so the refusal there is about establishment, not about calling.
    let program = [bump(), bump_caller("probe::below_100", true)];
    let (certified, reason) = graph_verdict(&program, "probe::below_100");
    assert!(certified, "a caller that establishes bump's requires must certify: {reason:?}");
}
