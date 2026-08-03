use trust_types::UnwindEdge;
use std::collections::BTreeSet;

use trust_types::fx::FxHashSet;
use trust_types::{
    AggregateKind, AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl,
    Operand, Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VariantDef,
    VcKind, VerifiableBody, VerifiableFunction,
};

use super::{
    StmtVersionCtx, VersionCtx, accumulator_init_const, block_def_establish_subsumes_kill,
    build_semantic_guard_map, flip_matches_kill_stmt, flip_token_distinctness_violations,
    formula_survives_redefs, generate_full_assert_refutation_vcs, reaching_def_versions,
    shadow_parity_disagreements, shadow_parity_disagreements_overlap, stmt_writes_name,
    v2_build_path_definition_map, v2_live_path_defs, v2_may_reassigned_per_block,
    version_rename_at,
};

/// `fn(a, b) { let m = if a < b { a } else { b }; if m < 1000 { .. } else { .. } }`
///   bb0: cmp0 = Lt(a, b);  SwitchInt(cmp0) -> [0: bb2, otherwise: bb1]
///   bb1 (a < b):  m = a;   goto bb3
///   bb2 (else):   m = b;   goto bb3
///   bb3 (join):   c = Lt(m, 1000);  SwitchInt(c) -> [0: bb5, otherwise: bb4]
///   bb4 (m<1000): return     <- the guarded block whose hypotheses we check
///   bb5 (else):   return
fn merge_then_guard_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "merge_then_guard".to_string(),
        def_path: "test::merge_then_guard".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("m".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("cmp0".into()) },
                LocalDecl { index: 5, ty: Ty::Bool, name: Some("c".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(3)),
                            Operand::Constant(ConstValue::Int(1000)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(5))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn defines(defs: &[Formula], var: &str) -> bool {
    // Version-aware: the S2c flip versions a threaded def's subject
    // (`lo` -> `lo#s0_0`); "defines `lo`" means a def of that PLACE at any version.
    defs.iter().any(|f| {
        matches!(f, Formula::Eq(lhs, _)
            if lhs.var_name().map(|n| n.split('#').next().unwrap_or(n)) == Some(var))
    })
}

fn defines_as_ite(defs: &[Formula], var: &str) -> bool {
    defs.iter().any(|f| {
        matches!(f, Formula::Eq(lhs, rhs)
            if lhs.var_name() == Some(var) && matches!(rhs.as_ref(), Formula::Ite(..)))
    })
}

fn mentions(defs: &[Formula], var: &str) -> bool {
    defs.iter().any(|f| f.free_variables().contains(var))
}

fn checked_assert_with_cleanup(cleanup: BlockId) -> VerifiableFunction {
    VerifiableFunction {
        name: "checked_assert_cleanup".into(),
        def_path: "test::checked_assert_cleanup".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                    name: Some("checked".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Cleanup(cleanup),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Resume },
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

fn option_u64_ty() -> Ty {
    Ty::Adt {
        adt_kind: None,
        layout: None,
        name: "core::option::Option".into(),
        fields: vec![
            ("__tag".into(), Ty::Int { width: 64, signed: true }),
            ("__v1_0".into(), Ty::u64()),
        ],
        variants: vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), Ty::u64())],
            },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    }
}

fn probe_call_with_cleanup(cleanup: BlockId) -> VerifiableFunction {
    let option = option_u64_ty();
    VerifiableFunction {
        name: "probe_call_cleanup".into(),
        def_path: "test::probe_call_cleanup".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: option.clone(), name: Some("o".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(option) },
                    name: Some("recv".into()),
                },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("g".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        func: "core::option::Option::<T>::is_some".into(),
                        args: vec![Operand::Move(Place::local(2))],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        unwind: UnwindEdge::Cleanup(cleanup),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Resume },
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
fn assert_success_facts_never_flow_to_cleanup_or_mixed_join() {
    let distinct = v2_build_path_definition_map(&checked_assert_with_cleanup(BlockId(2)));
    let normal = distinct.get(&BlockId(1)).cloned().unwrap_or_default();
    let cleanup = distinct.get(&BlockId(2)).cloned().unwrap_or_default();
    assert!(
        mentions(&normal, "checked.0"),
        "normal Assert successor must receive the checked result equation: {normal:?}"
    );
    assert!(
        !mentions(&cleanup, "checked.0"),
        "Assert cleanup must not receive success-only checked facts: {cleanup:?}"
    );

    let coincident = v2_build_path_definition_map(&checked_assert_with_cleanup(BlockId(1)));
    let joined = coincident.get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        !mentions(&joined, "checked.0"),
        "normal==cleanup joins both outcomes and must intersect away success facts: {joined:?}"
    );
}

#[test]
fn call_return_facts_never_flow_to_cleanup_or_mixed_join() {
    let distinct = v2_build_path_definition_map(&probe_call_with_cleanup(BlockId(2)));
    let normal = distinct.get(&BlockId(1)).cloned().unwrap_or_default();
    let cleanup = distinct.get(&BlockId(2)).cloned().unwrap_or_default();
    assert!(
        mentions(&normal, "g") && mentions(&normal, "o.0"),
        "normal Call successor must receive modeled post-return facts: {normal:?}"
    );
    assert!(
        !mentions(&cleanup, "g"),
        "Call cleanup must not observe a returned destination value: {cleanup:?}"
    );

    let coincident = v2_build_path_definition_map(&probe_call_with_cleanup(BlockId(1)));
    let joined = coincident.get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        !mentions(&joined, "g"),
        "normal==cleanup joins both outcomes and must intersect away call-return facts: {joined:?}"
    );
}

fn overflow_cleanup_asserts_wrapped_result() -> VerifiableFunction {
    VerifiableFunction {
        name: "overflow_cleanup_asserts_wrapped_result".into(),
        def_path: "test::overflow_cleanup_asserts_wrapped_result".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                    name: Some("checked".into()),
                },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("wrapped_is_zero".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Cleanup(BlockId(2)),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::field(3, 0)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::panicking::panic_fmt".into(),
                        args: vec![],
                        dest: Place::local(0),
                        target: None,
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        unwind: UnwindEdge::Terminate,
                    },
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Resume },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![
            Formula::Eq(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Int(u32::MAX as i128)),
            ),
            Formula::Eq(
                Box::new(Formula::Var("b".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            ),
        ],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn overflow_cleanup_never_gets_false_unbounded_result_equation() {
    let func = overflow_cleanup_asserts_wrapped_result();
    let defs = super::guards::extract_overflow_flag_semantics(&func, &func.body.blocks[0]);
    assert!(
        !mentions(&defs, "checked.0") && mentions(&defs, "checked.1"),
        "failure-edge semantics may define only the exact flag, never the wrapped value: {defs:?}"
    );
    assert!(
        generate_full_assert_refutation_vcs(&func).is_empty(),
        "a cleanup assertion over wrapped checked.0 must stay ungrounded; a global \
         checked.0 == unbounded(a+b) equation would falsely prove it unreachable"
    );
}

#[test]
fn guard_comparison_survives_into_guarded_block_past_join() {
    let func = merge_then_guard_fn();
    let map = v2_build_path_definition_map(&func);
    let guarded = map.get(&BlockId(4)).cloned().unwrap_or_default();

    // (a) The dominating comparison `c == (m < 1000)` established at the join
    // must reach the guarded block, or the guard cannot constrain `m`.
    assert!(
        defines(&guarded, "c"),
        "guarded block bb4 must retain the join-established comparison def for `c`; \
         got {guarded:?}"
    );
    // (b) Soundness: the BARE per-arm copies `m == a` / `m == b` hold on only one
    // arm and must NOT survive the intersection as unconditional defs. A surviving
    // bare non-Ite def of `m` downstream is exactly the stale-leak hole this test
    // guards. The UNCONDITIONAL merged `m == Ite(..)`, by contrast, is true on every
    // path through the dominating join bb3 and IS allowed to propagate.
    for rhs in def_rhs(&guarded, "m") {
        assert!(
            matches!(rhs, Formula::Ite(..)),
            "bb4 must not retain a bare path-specific def of `m` (e.g. `m == a`); \
             only the unconditional merged Ite may propagate. got def `m == {rhs:?}`"
        );
    }
    // (b') downstream propagation: the merged Ite established at the
    // dominating join bb3 reaches the guarded successor bb4. (Before #43 the join
    // Ite was deliberately not propagated; it is now sound to do so because the
    // fixpoint kills it on any reassignment of `m` or a guard var and the
    // intersection drops it at any block bb3 does not dominate.)
    assert!(
        defines_as_ite(&guarded, "m"),
        "bb4 (dominated by the join bb3, `m` unmodified) must carry the propagated \
         merge invariant `m == Ite(..)`; got {guarded:?}"
    );
}

#[test]
fn branch_merge_invariant_stays_attached_to_join_block() {
    let func = merge_then_guard_fn();
    let map = v2_build_path_definition_map(&func);
    let join = map.get(&BlockId(3)).cloned().unwrap_or_default();

    // (c) #18/#25: the join block's own hypotheses still carry `m == Ite(..)`.
    assert!(
        defines_as_ite(&join, "m"),
        "join block bb3 must still carry the branch-merge invariant `m == Ite(..)`; \
         got {join:?}"
    );
}

/// `fn(a, b) { let mut s = 0; if a < 100 { s = 50; } s + b }`
///   bb0:  s = 0;  cmp = Lt(a, 100);  SwitchInt(cmp) -> [0: bb2, otherwise: bb1]
///   bb1 (a<100):  s = 50;  goto bb2
///   bb2 (join):   return            <- the `s + b` overflow lives here in real MIR
///
/// This is the if-without-else shape: the skip edge (`cmp == 0`, i.e. a>=100)
/// jumps straight from the switch bb0 to the join bb2, so bb0 is one of bb2's
/// predecessors. It regressed as a SOUNDNESS HOLE: a stale `s == 0` from bb0
/// survived the join intersection and false-PROVED the unguarded `s + b`.
fn if_without_else_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "if_without_else".to_string(),
        def_path: "test::if_without_else".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("s".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("cmp".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(100)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(50))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn def_rhs<'a>(defs: &'a [Formula], var: &str) -> Vec<&'a Formula> {
    defs.iter()
        .filter_map(|f| match f {
            Formula::Eq(lhs, rhs) if lhs.var_name() == Some(var) => Some(rhs.as_ref()),
            _ => None,
        })
        .collect()
}

#[test]
fn if_without_else_join_carries_ite_not_stale_const() {
    let func = if_without_else_fn();
    let map = v2_build_path_definition_map(&func);
    let join = map.get(&BlockId(2)).cloned().unwrap_or_default();

    // Precision: the if-without-else skip edge must recover `s == Ite(..)` so a
    // safe `if c { s = K; } s + 1` still proves.
    assert!(
        defines_as_ite(&join, "s"),
        "join bb2 must carry the if-without-else merge `s == Ite(..)`; got {join:?}"
    );
    // Soundness: NO stale straight-line value of `s` may survive to the join.
    // A surviving `s == 0` (from bb0, before the conditional `s = 50`) is exactly
    // what false-PROVED the unguarded `s + b`. Every def of `s` here must be the
    // merged Ite — never a bare constant.
    for rhs in def_rhs(&join, "s") {
        assert!(
            matches!(rhs, Formula::Ite(..)),
            "join bb2 must not retain a stale non-Ite def of `s` (e.g. `s == 0`); \
             got def `s == {rhs:?}`"
        );
    }
}

/// `fn safe_cond_reassign(hi, c) { let mut lo = hi; if c { lo = 0; } hi - lo }`
///   bb0:  lo = hi;                  goto bb1   <- initialiser in an ANCESTOR
///   bb1:  SwitchInt(c) -> [0: bb3], otherwise: bb2
///   bb2 (c != 0):  lo = 0;          goto bb3
///   bb3 (join):    return                      <- `hi - lo` overflow lives here
///
/// Real rustc MIR for `safe_cond_reassign` has this shape: the first `hi - lo`
/// CheckedSub assert ends the init block, so the switch sits in bb1 while
/// `lo = hi` lives in the ancestor bb0. The switch block bb1 does NOT itself
/// assign `lo`. The earlier `if_without_else_fn` shape (initialiser in the
/// switch block) was already handled; this is the variant the pre-existing path
/// missed, leaving `lo` a free variable that false-FAILed the safe `hi - lo`.
/// The skip-edge augmentation must recover `lo == Ite(c == 0, hi, 0)` by reading
/// `lo`'s incoming dominating value (`lo == hi`) from the switch block's
/// converged entry facts.
fn if_without_else_ancestor_init_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "if_without_else_ancestor_init".to_string(),
        def_path: "test::if_without_else_ancestor_init".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("hi".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("c".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("lo".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn if_without_else_ancestor_init_recovers_ite() {
    let func = if_without_else_ancestor_init_fn();
    let map = v2_build_path_definition_map(&func);
    let join = map.get(&BlockId(3)).cloned().unwrap_or_default();

    // Precision: even though the switch block bb1 does not assign `lo`, the
    // skip-edge augmentation must merge `lo` into an Ite using its incoming
    // dominating value `hi`, so the safe `hi - lo` proves.
    assert!(
        defines_as_ite(&join, "lo"),
        "join bb3 must carry the ancestor-init merge `lo == Ite(..)`; got {join:?}"
    );
    // Soundness: `lo` differs across the two paths (hi vs 0), so no bare
    // straight-line value may survive the intersection. Every def of `lo` at the
    // join must be the merged Ite — never a bare `lo == hi` or `lo == 0`, either
    // of which would unsoundly constrain the join.
    for rhs in def_rhs(&join, "lo") {
        assert!(
            matches!(rhs, Formula::Ite(..)),
            "join bb3 must not retain a stale non-Ite def of `lo`; got def `lo == {rhs:?}`"
        );
    }
}

/// `fn(a, b) { let mut x = 0; let mut y = 0; if a<10 {x=5;} if b<10 {y=5;} x+y }`
///   bb0:  x = 0;  y = 0;  cmp0 = Lt(a, 10);  SwitchInt(cmp0) -> [0: bb2], else bb1
///   bb1 (a<10):  x = 5;                        goto bb2
///   bb2 (join1): cmp1 = Lt(b, 10);  SwitchInt(cmp1) -> [0: bb4], else bb3
///   bb3 (b<10):  y = 5;                        goto bb4
///   bb4 (join2): return        <- the `x + y` overflow lives here in real MIR
///
/// Two chained if-without-else merges feeding a single downstream use. `x` is
/// merged into an Ite at join1 (bb2); `y` is merged at join2 (bb4). For the
/// `x + y` VC at bb4 to prove, the join1 invariant `x == Ite(..)` must PROPAGATE
/// from bb2 down to bb4 — bb2 dominates bb4 and `x` is never reassigned between
/// them, so the propagation is sound. This is the downstream-propagation
/// target; before it, the join-local-only scheme left `x` a free variable at bb4
/// and the safe `x + y` false-FAILed.
fn two_chained_skips_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "two_chained_skips".to_string(),
        def_path: "test::two_chained_skips".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 5, ty: Ty::Bool, name: Some("cmp0".into()) },
                LocalDecl { index: 6, ty: Ty::Bool, name: Some("cmp1".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(10)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(5))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(10)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(6)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(5))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn chained_skip_join_ite_propagates_to_downstream_join() {
    let func = two_chained_skips_fn();
    let map = v2_build_path_definition_map(&func);
    let join2 = map.get(&BlockId(4)).cloned().unwrap_or_default();

    // downstream propagation: the join1 (bb2) invariant `x == Ite(..)`
    // must reach join2 (bb4), where the `x + y` use lives. bb2 dominates bb4 and
    // `x` is never reassigned between them, so this is sound — and necessary for
    // the safe `x + y` to prove.
    assert!(
        defines_as_ite(&join2, "x"),
        "join2 bb4 must carry the PROPAGATED join1 invariant `x == Ite(..)`; got {join2:?}"
    );
    // bb4's own if-without-else merge for `y` (ancestor-init skip edge: y == 0 from
    // bb0) must also be present.
    assert!(
        defines_as_ite(&join2, "y"),
        "join2 bb4 must carry its own merge `y == Ite(..)`; got {join2:?}"
    );
    // Soundness: `x` and `y` each differ across their merge arms, so NO bare
    // straight-line value may survive at bb4 — every def must be the merged Ite.
    // A surviving bare `x == 0` / `x == 5` (or `y == ..`) would unsoundly constrain
    // the downstream `x + y`.
    for var in ["x", "y"] {
        for rhs in def_rhs(&join2, var) {
            assert!(
                matches!(rhs, Formula::Ite(..)),
                "bb4 must not retain a stale non-Ite def of `{var}`; got def `{var} == {rhs:?}`"
            );
        }
    }
}

/// a chained `a + b +...` lowers to one Assert-guarded
/// CheckedBinaryOp per add, in SEPARATE blocks; the second block reads the
/// first add's tuple result (`r = t.0`). The first add's result definition
/// (`t.0 == a + b`) must cross the Assert-success edge into the consumer block,
/// or the second add sees an unconstrained `r` and false-FAILs.
///   bb0: t = CheckedAdd(a, b);  Assert(!t.1) -> bb1
///   bb1: r = move t.0;          goto bb2       <- consumer: must carry t.0 == a+b
///   bb2: a = big;               goto bb3       <- reassigns operand a
///   bb3: return                                <- t.0 == a+b must be KILLED here
fn chained_add_chain_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "chained_add_chain".to_string(),
        def_path: "test::chained_add_chain".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("r".into()) },
                LocalDecl {
                    index: 4,
                    ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                    name: Some("t".into()),
                },
                LocalDecl { index: 5, ty: Ty::u32(), name: Some("big".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::field(4, 1)),
                        expected: false,
                        msg: trust_types::AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Move(Place::field(4, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn chained_add_result_def_propagates_to_consumer_then_dies_on_operand_redef() {
    let func = chained_add_chain_fn();
    let map = v2_build_path_definition_map(&func);

    // Precision: the Assert-success result definition `t.0 == a + b` from
    // bb0 must reach the consumer block bb1, where `r = t.0` connects it onward.
    let consumer = map.get(&BlockId(1)).cloned().unwrap_or_default();
    let t0_rhs = def_rhs(&consumer, "t.0");
    assert!(
        t0_rhs.iter().any(|rhs| matches!(rhs, Formula::Add(..))),
        "bb1 must carry the propagated result def `t.0 == a + b`; got {consumer:?}"
    );

    // Soundness: the result def holds only while its operands are unchanged.
    // bb2 reassigns operand `a`, so the fact must be KILLED before bb3 — a
    // surviving `t.0 == a + b` over the NEW `a` would be a stale false fact.
    let after_redef = map.get(&BlockId(3)).cloned().unwrap_or_default();
    assert!(
        !defines(&after_redef, "t.0"),
        "bb3 must NOT carry `t.0 == ..` after bb2 reassigns operand `a`; got {after_redef:?}"
    );

    // Soundness: the entry block stores only its (empty) incoming intersection,
    // never the success-edge result def — that fact lives strictly in the outflow.
    let producer = map.get(&BlockId(0)).cloned().unwrap_or_default();
    assert!(
        !defines(&producer, "t.0"),
        "bb0 (entry) must not retroactively carry the success-edge result def; got {producer:?}"
    );
}

/// `fn(flag) { let r = if flag { Ok(10) } else { Err(20) };
///                        match r { Ok(x) => x + 1, Err(e) => e + 1 } }`
///   bb0: SwitchInt(flag) -> [0: bb2], otherwise: bb1
///   bb1 (then): r = Adt{variant 0 = Ok}([10]);   goto bb3
///   bb2 (else): r = Adt{variant 1 = Err}([20]);  goto bb3
///   bb3 (join): d = Discriminant(r);  SwitchInt(d) -> [0: bb4], otherwise: bb5
///   bb4 (Ok arm):  x = (r as Ok).0;   return    <- must carry `r@0.0 == 10`
///   bb5 (Err arm): e = (r as Err).0;  return    <- must carry `r@1.0 == 20`
///
/// Each construction's payload fact holds on ONE predecessor only, so the
/// intersection at the construction-join bb3 drops it; the matched arm then
/// reads an unconstrained payload and a safe `x + 1` / `e + 1` false-FAILs.
/// The de-mux re-routes each construction's payload to the arm that downcasts
/// its variant (the discriminant switch makes the variant-`k` arm reachable
/// only when `r` was built as variant `k`). The enum local's `Ty` is irrelevant
/// to routing/naming, so it is left as a plain `u32` placeholder here.
fn enum_demux_result_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "enum_demux_result".to_string(),
        def_path: "test::enum_demux_result".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("r".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("e".into()) },
                LocalDecl { index: 5, ty: Ty::u32(), name: Some("d".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Result".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Constant(ConstValue::Int(10))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Result".into(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Constant(ConstValue::Int(20))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::Discriminant(Place::local(2)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(5),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 2,
                            projections: vec![Projection::Downcast(0), Projection::Field(0)],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 2,
                            projections: vec![Projection::Downcast(1), Projection::Field(0)],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn enum_construction_demux_routes_payload_to_matching_arm() {
    let func = enum_demux_result_fn();
    let demux = super::guards::enum_construction_demux_definitions(&func);

    // Precision: the Ok arm (bb4, downcasts variant 0) must receive variant 0's
    // payload `r@0.0 == 10` so the safe `x + 1` proves.
    let ok_arm = demux.get(&BlockId(4)).cloned().unwrap_or_default();
    assert!(
        ok_arm.iter().any(|f| matches!(f, Formula::Eq(l, r)
            if l.var_name() == Some("r@0.0") && matches!(r.as_ref(), Formula::Int(10)))),
        "Ok arm bb4 must carry routed payload `r@0.0 == 10`; got {ok_arm:?}"
    );
    // De-mux correctness: the Ok arm must NOT receive the OTHER variant's payload
    // — routing `r@1.0` here (unreachable on this arm) would be incoherent.
    assert!(
        !ok_arm.iter().any(|f| matches!(f, Formula::Eq(l, _) if l.var_name() == Some("r@1.0"))),
        "Ok arm bb4 must NOT carry the other variant's payload `r@1.0`; got {ok_arm:?}"
    );

    // Symmetric for the Err arm (bb5, downcasts variant 1): `r@1.0 == 20`, no `r@0.0`.
    let err_arm = demux.get(&BlockId(5)).cloned().unwrap_or_default();
    assert!(
        err_arm.iter().any(|f| matches!(f, Formula::Eq(l, r)
            if l.var_name() == Some("r@1.0") && matches!(r.as_ref(), Formula::Int(20)))),
        "Err arm bb5 must carry routed payload `r@1.0 == 20`; got {err_arm:?}"
    );
    assert!(
        !err_arm
            .iter()
            .any(|f| matches!(f, Formula::Eq(l, _) if l.var_name() == Some("r@0.0"))),
        "Err arm bb5 must NOT carry the other variant's payload `r@0.0`; got {err_arm:?}"
    );
}

/// SOUNDNESS probe: `if flag { Some(a) } else { Some(b) }` — BOTH
/// predecessors construct the SAME variant with DIFFERENT payloads.
///   bb0: SwitchInt(flag) -> [0: bb2], otherwise: bb1
///   bb1: r = Adt{variant 0 = Some}([a]);  goto bb3
///   bb2: r = Adt{variant 0 = Some}([b]);  goto bb3
///   bb3: d = Discriminant(r);  SwitchInt(d) -> [0: bb4], otherwise: bb5
///   bb4 (Some arm): x = (r as Some).0;  return
///   bb5 (None arm): return
///
/// The matched payload is `a` on one path and `b` on the other, so NO single
/// equality is true at the arm. Routing either would let the solver pick the
/// value that vacuously discharges a real `x + 1` overflow — a false-PROVE.
/// The duplicate-variant guard must drop variant 0 entirely.
fn enum_demux_duplicate_variant_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "enum_demux_duplicate_variant".to_string(),
        def_path: "test::enum_demux_duplicate_variant".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("r".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 5, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 6, ty: Ty::u32(), name: Some("d".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Option".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Copy(Place::local(3))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Option".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Copy(Place::local(4))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::Discriminant(Place::local(2)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(6)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(5),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 2,
                            projections: vec![Projection::Downcast(0), Projection::Field(0)],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn enum_construction_demux_skips_nonunique_variant_payload() {
    let func = enum_demux_duplicate_variant_fn();
    let demux = super::guards::enum_construction_demux_definitions(&func);

    // Soundness: two predecessors build variant 0 with different payloads (a vs
    // b), so the payload is not unique at the Some arm. The de-mux must route NO
    // `r@0.0`; a routed equality would be true on only one path yet asserted on
    // both, vacuously discharging a real overflow on the matched value.
    let some_arm = demux.get(&BlockId(4)).cloned().unwrap_or_default();
    assert!(
        !some_arm
            .iter()
            .any(|f| matches!(f, Formula::Eq(l, _) if l.var_name() == Some("r@0.0"))),
        "Some arm bb4 must NOT carry a routed payload for the non-unique variant 0; \
         got {some_arm:?}"
    );
}

#[test]
fn enum_construction_demux_inert_on_plain_branch_merge() {
    // A non-enum SwitchInt diamond (the `merge_then_guard` shape: the switch is
    // on a `Lt` comparison, not a `Discriminant`) has no ADT construction feeding
    // its joins, so the de-mux must route nothing — it fires ONLY for genuine
    // construction-then-discriminant-switch joins.
    assert!(
        super::guards::enum_construction_demux_definitions(&merge_then_guard_fn()).is_empty(),
        "de-mux must be inert on a non-enum branch-merge diamond"
    );
}

/// `flag_some` shape: `let o = if flag { if v < 100 { Some(v) } else { None } }
/// else { None };  match o { Some(x) => x + 1, None => 0 }`. The Some
/// constructor (bb2) has a UNIQUE predecessor bb1 whose `v < 100` switch guards
/// the construction; the None constructor (bb3) is SHARED by the flag-false and
/// guard-false paths (two predecessors). bb6 is the Some arm.
fn enum_demux_guarded_some_fn() -> VerifiableFunction {
    let some_payload =
        Place { local: 3, projections: vec![Projection::Downcast(1), Projection::Field(0)] };
    VerifiableFunction {
        name: "enum_demux_guarded_some".to_string(),
        def_path: "test::enum_demux_guarded_some".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("v".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("opt".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("g".into()) },
                LocalDecl { index: 5, ty: Ty::u32(), name: Some("d".into()) },
                LocalDecl { index: 6, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![
                // bb0: if flag { bb1 } else { bb3 }
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: g = v < 100; if g { bb2 } else { bb3 }
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(100)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb2: opt = Some(v); goto bb4
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Option".into(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Copy(Place::local(2))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                // bb3: opt = None; goto bb4  (shared: preds = [bb0, bb1])
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Option".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                // bb4: d = discriminant(opt); switch -> [0: bb5(None), 1: bb6(Some)]
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::Discriminant(Place::local(3)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(5)), (1, BlockId(6))],
                        otherwise: BlockId(7),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb5: None arm
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                // bb6: Some arm — x = opt.downcast(1).field(0)
                BasicBlock {
                    id: BlockId(6),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::Use(Operand::Copy(some_payload)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(7),
                    stmts: vec![],
                    terminator: Terminator::Unreachable,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn enum_construction_demux_routes_edge_guard_to_matching_arm() {
    let func = enum_demux_guarded_some_fn();
    let demux = super::guards::enum_construction_demux_definitions(&func);

    // The Some arm (bb6, downcasts variant 1) must carry BOTH the payload
    // `opt@1.0 == v` AND the construction-edge guard `v < 100`. Together they
    // let the safe `x + 1` (x == v < 100) prove, where payload-alone would
    // leave x unconstrained and false-FAIL.
    let some_arm = demux.get(&BlockId(6)).cloned().unwrap_or_default();
    assert!(
        some_arm
            .iter()
            .any(|f| matches!(f, Formula::Eq(l, _) if l.var_name() == Some("opt@1.0"))),
        "Some arm bb6 must carry routed payload `opt@1.0 == v`; got {some_arm:?}"
    );
    assert!(
        some_arm.iter().any(|f| matches!(f, Formula::Lt(l, r)
            if l.var_name() == Some("v") && matches!(r.as_ref(), Formula::Int(100)))),
        "Some arm bb6 must carry routed edge guard `v < 100`; got {some_arm:?}"
    );

    // De-mux correctness: the None arm (bb5) must NOT receive the Some path's
    // `v < 100` guard — it is reachable only when `opt` is None.
    let none_arm = demux.get(&BlockId(5)).cloned().unwrap_or_default();
    assert!(
        !none_arm.iter().any(|f| matches!(f, Formula::Lt(l, _) if l.var_name() == Some("v"))),
        "None arm bb5 must NOT carry the Some-path guard `v < 100`; got {none_arm:?}"
    );
}

/// A Some constructor (bb4) reached by TWO predecessors (bb1, bb2) — its
/// incoming edge guard is ambiguous, so no guard may be routed — while the None
/// constructor (bb3) is single-pred. The payload (`opt@1.0 == v`) still routes
/// because payload soundness does not depend on the constructor's pred count.
fn enum_demux_multipred_some_fn() -> VerifiableFunction {
    let some_payload =
        Place { local: 3, projections: vec![Projection::Downcast(1), Projection::Field(0)] };
    VerifiableFunction {
        name: "enum_demux_multipred_some".to_string(),
        def_path: "test::enum_demux_multipred_some".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("sel".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("v".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("opt".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("d".into()) },
                LocalDecl { index: 5, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![
                // bb0: switch sel -> [0: bb1, 1: bb2] else bb3(None)
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
                // bb1 -> bb4 (into Some constructor)
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                // bb2 -> bb4 (into Some constructor)
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                // bb3: opt = None; goto bb5  (single-pred None constructor)
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Option".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                // bb4: opt = Some(v); goto bb5  (preds = [bb1, bb2] -> ambiguous guard)
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Option".into(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Copy(Place::local(2))],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                // bb5: d = discriminant(opt); switch -> [0: bb6(None), 1: bb7(Some)]
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Discriminant(Place::local(3)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(6)), (1, BlockId(7))],
                        otherwise: BlockId(8),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(6),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(7),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::Use(Operand::Copy(some_payload)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(8),
                    stmts: vec![],
                    terminator: Terminator::Unreachable,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn enum_construction_demux_skips_guard_for_multipred_constructor() {
    let func = enum_demux_multipred_some_fn();
    let demux = super::guards::enum_construction_demux_definitions(&func);
    let some_arm = demux.get(&BlockId(7)).cloned().unwrap_or_default();

    // Payload still routes (does not depend on the constructor's pred count).
    assert!(
        some_arm
            .iter()
            .any(|f| matches!(f, Formula::Eq(l, _) if l.var_name() == Some("opt@1.0"))),
        "Some arm bb7 must still carry routed payload `opt@1.0 == v`; got {some_arm:?}"
    );
    // Soundness: the Some constructor bb4 has two predecessors, so NO edge guard
    // is unambiguous — none may be routed. A routed guard from only one edge
    // would be asserted on a path it does not hold for, a false-PROVE risk.
    assert!(
        some_arm.iter().all(|f| !matches!(
            f,
            Formula::Lt(..) | Formula::Le(..) | Formula::Gt(..) | Formula::Ge(..)
        )),
        "Some arm bb7 must carry NO routed comparison guard (ambiguous edge); got {some_arm:?}"
    );
}

/// Nested-aggregate payload: `if flag && a < 100 { Some((a, b)) } else { None }`
/// then `match { Some((x, _)) => x + 1, .. }`. The Some constructor builds the
/// tuple temp first (`_6 = (a, b); opt = Some(_6)`), so the routed payload fact is
/// the whole-tuple `opt@1.0 == _6`, but the arm reads the nested leaf `opt@1.0.0`.
/// The de-mux must expand the whole-tuple equality into leaf equalities
/// (`opt@1.0.0 == a`) so the routed guard `a < 100` can discharge `x + 1`.
fn enum_demux_tuple_payload_fn() -> VerifiableFunction {
    let some_payload = Place {
        local: 4,
        projections: vec![Projection::Downcast(1), Projection::Field(0), Projection::Field(0)],
    };
    VerifiableFunction {
        name: "enum_demux_tuple_payload".to_string(),
        def_path: "test::enum_demux_tuple_payload".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("opt".into()) },
                LocalDecl { index: 5, ty: Ty::Bool, name: Some("g".into()) },
                LocalDecl { index: 6, ty: Ty::Tuple(vec![Ty::u32(), Ty::u32()]), name: None },
                LocalDecl { index: 7, ty: Ty::u32(), name: Some("d".into()) },
                LocalDecl { index: 8, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![
                // bb0: if flag { bb1 } else { bb3 }
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: g = a < 100; if g { bb2 } else { bb3 }
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(100)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb2: _6 = (a, b); opt = Some(_6); goto bb4
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Tuple,
                                vec![
                                    Operand::Copy(Place::local(2)),
                                    Operand::Copy(Place::local(3)),
                                ],
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: "Option".into(),
                                    variant: 1,
                                    active_field: None,
                                    args: None,
                                },
                                vec![Operand::Move(Place::local(6))],
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                // bb3: opt = None; goto bb4  (shared: preds = [bb0, bb1])
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Option".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                // bb4: d = discriminant(opt); switch -> [0: bb5(None), 1: bb6(Some)]
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(7),
                        rvalue: Rvalue::Discriminant(Place::local(4)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(7)),
                        targets: vec![(0, BlockId(5)), (1, BlockId(6))],
                        otherwise: BlockId(7),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb5: None arm
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                // bb6: Some arm — x = opt.downcast(1).field(0).field(0)
                BasicBlock {
                    id: BlockId(6),
                    stmts: vec![Statement::Assign {
                        place: Place::local(8),
                        rvalue: Rvalue::Use(Operand::Copy(some_payload)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(7),
                    stmts: vec![],
                    terminator: Terminator::Unreachable,
                },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn enum_construction_demux_expands_nested_tuple_payload_leaf() {
    let func = enum_demux_tuple_payload_fn();
    let demux = super::guards::enum_construction_demux_definitions(&func);
    let some_arm = demux.get(&BlockId(6)).cloned().unwrap_or_default();

    // The whole-tuple equality is kept (additive)...
    assert!(
        some_arm
            .iter()
            .any(|f| matches!(f, Formula::Eq(l, _) if l.var_name() == Some("opt@1.0"))),
        "Some arm bb6 should keep the whole-tuple payload `opt@1.0 == _6`; got {some_arm:?}"
    );
    // ...AND the nested leaf `opt@1.0.0 == a` is synthesized so the arm read of
    // `opt@1.0.0` is constrained to the leaf source `a`.
    assert!(
        some_arm.iter().any(|f| matches!(f, Formula::Eq(l, r)
            if l.var_name() == Some("opt@1.0.0") && r.var_name() == Some("a"))),
        "Some arm bb6 must carry expanded leaf `opt@1.0.0 == a`; got {some_arm:?}"
    );
    // ...AND the routed construction-edge guard `a < 100`, which (with the leaf)
    // discharges `x + 1`.
    assert!(
        some_arm.iter().any(|f| matches!(f, Formula::Lt(l, r)
            if l.var_name() == Some("a") && matches!(r.as_ref(), Formula::Int(100)))),
        "Some arm bb6 must carry routed edge guard `a < 100`; got {some_arm:?}"
    );
}

/// `fn(m0, big) { let mut m = m0; let c = m < 1000; m = big; ... }`
///   bb0:  m = m0;  c = Lt(m, 1000);  goto bb1
///   bb1:  m = big;                   goto bb2
///   bb2:  return     <- a later `if c { m + 1 }` would live downstream of here
///
/// The comparison `c == (m < 1000)` is established in bb0 but its operand `m`
/// is overwritten in bb1. The fact must NOT reach bb2: keeping it lets a
/// downstream guard `if c` constrain the *new* `m` via the stale comparison
/// and vacuously discharge `m + 1` even though `m` is now unbounded.
fn cross_block_stale_cmp_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "cross_block_stale_cmp".to_string(),
        def_path: "test::cross_block_stale_cmp".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("m0".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("big".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("m".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("c".into()) },
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
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Int(1000)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn stale_comparison_dies_when_operand_reassigned_in_later_block() {
    let func = cross_block_stale_cmp_fn();
    let map = v2_build_path_definition_map(&func);
    let downstream = map.get(&BlockId(2)).cloned().unwrap_or_default();

    // Soundness: the comparison over the now-overwritten `m` must not survive.
    assert!(
        !defines(&downstream, "c"),
        "bb2 must NOT retain `c == (m < 1000)` after `m` is reassigned in bb1; \
         a surviving stale comparison vacuously discharges a downstream `m + 1`; \
         got {downstream:?}"
    );
    // The live reassignment is still available.
    assert!(
        defines(&downstream, "m"),
        "bb2 must retain the live `m == big`; got {downstream:?}"
    );
}

// Trust: regression for the build_semantic_guard_map stale-fact false-PROVE
// (e2e probe: sem_stale_sub). bb0 defines `lo == hi`; the BFS guard map
// threads that def forward into bb1's entry guards. When `reassign_lo_in_bb1`
// is set, bb1 then reassigns `lo = big`, which invalidates the inherited
// `lo == hi`. Left alive, that stale def is conjoined to bb1's own `hi - lo`
// VC and vacuously discharges a real underflow.
fn sem_stale_blockdef_fn(reassign_lo_in_bb1: bool) -> VerifiableFunction {
    let bb1_stmts = if reassign_lo_in_bb1 {
        vec![Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
            span: SourceSpan::default(),
        }]
    } else {
        vec![]
    };
    VerifiableFunction {
        name: "sem_stale_blockdef".to_string(),
        def_path: "test::sem_stale_blockdef".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("hi".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("big".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("lo".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: bb1_stmts,
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn semantic_guard_map_kills_block_def_on_operand_reassignment() {
    let func = sem_stale_blockdef_fn(true);
    let map = build_semantic_guard_map(&func);
    // bb1 reassigns `lo`; the inherited `lo == hi` from bb0 must NOT be one
    // of bb1's entry guards — it is stale the moment bb1 runs `lo = big`,
    // and conjoined to bb1's own `hi - lo` it false-PROVES a real underflow.
    let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        !bb1.iter().any(|f| f.free_variables().contains("lo")),
        "bb1 must NOT carry an inherited fact mentioning the reassigned `lo`; got {bb1:?}"
    );
}

#[test]
fn semantic_guard_map_keeps_block_def_when_operand_live() {
    // Control: bb1 does NOT reassign `lo`, so `lo == hi` is live and must
    // reach bb1 — guards the kill against over-dropping live facts.
    let func = sem_stale_blockdef_fn(false);
    let map = build_semantic_guard_map(&func);
    let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        defines(&bb1, "lo"),
        "bb1 must retain the live `lo == hi` when `lo` is never reassigned; got {bb1:?}"
    );
}

/// bb0: `x = 3; r = &mut x; [r = &mut x;] *r = 4e9; goto bb1`. With `reseat`,
/// the SECOND `&mut x` makes `unique_whole_local_def(r)=None` so `*r=4e9` names
/// the opaque `r*` (NOT `x`) — and `extract_block_definitions` still emits the
/// stale `Eq(x, 3)`, which `build_semantic_guard_map` threads to bb1 raw.
fn sem_reseat_havoc_fn(reseat: bool) -> VerifiableFunction {
    use trust_types::Projection;
    let mut bb0 = vec![
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 32))),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
            span: SourceSpan::default(),
        },
    ];
    if reseat {
        bb0.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
            span: SourceSpan::default(),
        });
    }
    bb0.push(Statement::Assign {
        place: Place { local: 2, projections: vec![Projection::Deref] },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(4_000_000_000, 32))),
        span: SourceSpan::default(),
    });
    VerifiableFunction {
        name: "sem_reseat_havoc".to_string(),
        def_path: "test::sem_reseat_havoc".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("r".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: bb0,
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn semantic_guard_map_drops_reseat_havoced_block_def() {
    // SOUNDNESS regression: the threaded block_defs must drop the stale
    // `Eq(x, 3)` once the reseated `*r = 4e9` havocs the referent `x`, else
    // bb1 inherits it and false-PROVEs a real violation over the live `x`.
    let func = sem_reseat_havoc_fn(true);
    let map = build_semantic_guard_map(&func);
    let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        !bb1.iter().any(|f| f.free_variables().contains("x")),
        "bb1 must not carry a stale x-fact after an opaque deref-store reseat; got {bb1:?}"
    );
}

#[test]
fn semantic_guard_map_keeps_block_def_single_borrow_store() {
    // Control: a SINGLE-borrow `*r = 4e9` canonicalizes to `x`, so the LIVE
    // `Eq(x, 4e9)` def must still reach bb1 (no over-conservatism — the havoc
    // fires only for the non-canonicalizable reseat).
    let func = sem_reseat_havoc_fn(false);
    let map = build_semantic_guard_map(&func);
    let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        defines(&bb1, "x"),
        "bb1 must retain the live x-fact for a single-borrow store; got {bb1:?}"
    );
}

/// Accumulator `acc = 0; acc = (acc + a).0` with an optional `&mut acc` escape.
/// The global `t <= init + K*M` accumulator-bound fact has no per-block kill, so
/// its whole soundness rests on the emission gate `accumulator_init_const`
/// fail-closing on any `&mut` / `&raw` of the accumulator (the only way a
/// `*p = huge` could violate the bound). Locks that gate.
fn accumulator_fn(escape: bool) -> VerifiableFunction {
    let mut stmts = vec![
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Copy(Place {
                local: 3,
                projections: vec![Projection::Field(0)],
            })),
            span: SourceSpan::default(),
        },
    ];
    if escape {
        stmts.push(Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
            span: SourceSpan::default(),
        });
    }
    VerifiableFunction {
        name: "acc_fn".to_string(),
        def_path: "test::acc_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("acc".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                    name: Some("ck".into()),
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("r".into()),
                },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
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
fn accumulator_bound_withheld_when_accumulator_escapes_via_mut_borrow() {
    // Escape via `&mut acc`: the emission gate must fail closed (None) so NO
    // `t <= init + K*M` bound fact is conjoined — a `*r = huge` could otherwise
    // violate it. This is what keeps the deref-store/escape class out of the
    // (per-block-kill-free) accumulator bound.
    assert_eq!(
        accumulator_init_const(&accumulator_fn(true), 1, 3),
        None,
        "a mutably-borrowed accumulator must not yield a const init (no bound fact)"
    );
    // Control: the IDENTICAL accumulator with NO escape IS recognized (init 0),
    // so the gate is what withholds the bound above — not a structural miss.
    assert_eq!(
        accumulator_init_const(&accumulator_fn(false), 1, 3),
        Some(0),
        "a non-escaping const-init self-add accumulator must be recognized"
    );
}

fn lo_eq_hi() -> Vec<Formula> {
    vec![Formula::Eq(
        Box::new(Formula::Var("lo".into(), Sort::Int)),
        Box::new(Formula::Var("hi".into(), Sort::Int)),
    )]
}

#[test]
fn live_path_defs_drops_entry_fact_reassigned_in_block() {
    // bb1 reassigns `lo`; the block-ENTRY fact `lo == hi` is stale for bb1's
    // own end-of-block `hi - lo` VC and must be dropped before it is
    // conjoined (otherwise it contradicts the live in-block `lo == big` and
    // vacuously discharges a real underflow).
    let func = sem_stale_blockdef_fn(true);
    let live = v2_live_path_defs(&func, &func.body.blocks[1], &lo_eq_hi());
    assert!(
        !live.iter().any(|f| f.free_variables().contains("lo")),
        "entry `lo == hi` must be dropped for a block that reassigns `lo`; got {live:?}"
    );
}

#[test]
fn live_path_defs_keeps_entry_fact_when_var_live() {
    // Control: bb1 never reassigns `lo`, so the entry fact stays live.
    let func = sem_stale_blockdef_fn(false);
    let live = v2_live_path_defs(&func, &func.body.blocks[1], &lo_eq_hi());
    assert!(
        defines(&live, "lo"),
        "entry `lo == hi` must survive a block that never reassigns `lo`; got {live:?}"
    );
}

// Trust: regression for the terminator-dest staleness hardening. bb0 defines
// `lo == hi`, then either reassigns `lo` via a `Call { dest: lo }` terminator
// (call_dest = true) or just `Goto`s (call_dest = false). The statement-based
// kill cannot see the terminator write, so without `terminator_def_names` the
// stale `lo == hi` would be threaded to bb1 and could false-PROVE there.
fn term_call_dest_fn(call_dest: bool) -> VerifiableFunction {
    let terminator = if call_dest {
        Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "make".to_string(),
            args: vec![Operand::Copy(Place::local(1))],
            dest: Place::local(3),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
        }
    } else {
        Terminator::Goto(BlockId(1))
    };
    VerifiableFunction {
        name: "term_call_dest".to_string(),
        def_path: "test::term_call_dest".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("hi".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("big".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("lo".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator,
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn semantic_guard_map_kills_terminator_call_dest() {
    // bb0 reassigns `lo` via a `Call { dest: lo }` terminator; the block def
    // `lo == hi` is stale for bb1 and must not be threaded there. The
    // statement-based kill cannot see the terminator write, so this exercises
    // `terminator_def_names`.
    let func = term_call_dest_fn(true);
    let map = build_semantic_guard_map(&func);
    let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        !bb1.iter().any(|f| f.free_variables().contains("lo")),
        "bb1 must NOT carry `lo == hi` past a `Call {{ dest: lo }}` terminator; got {bb1:?}"
    );
}

// Trust: LANE witness — PROJECTED Call dest. bb0 establishes `s.0 == hi` via a
// struct-field store, then reassigns `s.0` via `Call { dest: s.0 }`. The
// pre-call fact `s.0 == hi` is stale for bb1 and must be killed by the
// terminator-dest kill. `terminator_def_names` only pushes the dest name when
// `dest.projections.is_empty()`, so a PROJECTED dest is skipped and the stale
// `s.0 == hi` survives into bb1 — where it would vacuously discharge a real
// overflow/assert on the post-call `s.0`.
fn term_call_projected_dest_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "term_call_projected_dest".to_string(),
        def_path: "test::term_call_projected_dest".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("hi".into()) },
                // a struct/tuple local `s` with one u32 field `s.0`
                LocalDecl { index: 2, ty: Ty::Tuple(vec![Ty::u32()]), name: Some("s".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    // s.0 = hi  ⇒ establishes fact `s.0 == hi`
                    stmts: vec![Statement::Assign {
                        place: Place::field(2, 0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    // s.0 = make(hi)  ⇒ PROJECTED Call dest reassigns s.0
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "make".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::field(2, 0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn semantic_guard_map_kills_projected_terminator_call_dest() {
    // bb0 reassigns `s.0` via a `Call { dest: s.0 }` PROJECTED terminator; the
    // block def `s.0 == hi` is stale for bb1. Under the S2c flip it is threaded
    // ESTABLISH-VERSIONED (`s.0#s0_0`) but must be NAME-DISJOINT from the value
    // bb1 actually reads: the terminator-aware OUT token pins bb1's `s.0` to the
    // terminator marker `s.0#s0_t`, so the stale fact cannot constrain it.
    let func = term_call_projected_dest_fn();
    let map = build_semantic_guard_map(&func);
    let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
    // The variable bb1 reads for `s.0` (post-terminator value).
    let sv = StmtVersionCtx::build(&func);
    let live = match sv.version_token_at(&func, BlockId(1), 0, "s.0") {
        Some(tok) => format!("s.0#{tok}"),
        None => "s.0".to_string(),
    };
    assert!(
        !bb1.iter().any(|f| f.free_variables().contains(&live)),
        "bb1 must NOT carry a fact naming the post-terminator `{live}` (the stale \
         `s.0 == hi` must be version-disjoint from it); got {bb1:?}"
    );
    // And the stale fact, if threaded, must carry its pre-terminator establish
    // token (NOT the terminator token) — i.e. it is present-but-disconnected.
    let has_stale_disjoint = bb1
        .iter()
        .any(|f| f.free_variables().iter().any(|v| v.starts_with("s.0#") && *v != live));
    assert!(
        has_stale_disjoint
            || bb1.iter().all(|f| !f.free_variables().iter().any(|v| v.starts_with("s.0"))),
        "any threaded `s.0` fact must be version-disjoint from the live read; got {bb1:?}"
    );
}

#[test]
fn path_def_map_kills_projected_terminator_call_dest() {
    // Same witness via the v2 path-definition fixpoint, the OTHER threading
    // path that conjoins facts onto successor VCs.
    let func = term_call_projected_dest_fn();
    let map = v2_build_path_definition_map(&func);
    let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        !bb1.iter().any(|f| f.free_variables().iter().any(|v| v.starts_with("s.0"))),
        "bb1 path-defs must NOT carry `s.0 == hi` past a projected Call dest; got {bb1:?}"
    );
}

// Trust: LANE end-to-end false-PROVE. Models, with a PROJECTED Call dest:
//   requires hi <= 1000 {
//     s.0 = hi;            // fact: s.0 == hi
//     s.0 = make(hi);      // Call { dest: s.0 } — s.0 is now make()'s arbitrary u32
//     let r = s.0 + 1;     // CheckedAdd + Assert(Overflow) on the POST-call s.0
//   }
// The post-call `s.0` is unconstrained (make() may return u32::MAX), so the add
// can genuinely overflow. But the stale fact `s.0 == hi` survives the projected
// Call dest; conjoined with the live precondition `hi <= 1000` it pins
// `s.0 <= 1000`, making `NOT in_range(s.0 + 1)` UNSAT — the overflow VC reports
// safe. A false-PROVE of a real overflow.
fn projected_call_then_overflow_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "projected_call_then_overflow".to_string(),
        def_path: "test::projected_call_then_overflow".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("hi".into()) },
                LocalDecl { index: 2, ty: Ty::Tuple(vec![Ty::u32()]), name: Some("s".into()) },
                // checked-add result tuple (value, overflow-bit)
                LocalDecl {
                    index: 3,
                    ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                    name: Some("r".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::field(2, 0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "make".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::field(2, 0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    // r = CheckedAdd(s.0, 1)
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::field(2, 0)),
                            Operand::Constant(ConstValue::Int(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        // entry contract `hi <= 1000`
        preconditions: vec![Formula::Le(
            Box::new(Formula::Var("hi".into(), Sort::Int)),
            Box::new(Formula::Int(1000)),
        )],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn projected_call_dest_does_not_pin_postcall_overflow_operand() {
    // The overflow VC for `s.0 + 1` must NOT carry the stale `s.0 == hi`
    // equality — otherwise the live precondition `hi <= 1000` pins the
    // post-call `s.0` and vacuously discharges a real overflow.
    let func = projected_call_then_overflow_fn();
    let vcs = super::generate_vcs(&func);
    let overflow_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .expect("expected an ArithmeticOverflow VC for s.0 + 1");
    // The soundness property is that the post-call `s.0` is NOT pinned to the
    // entry `hi` by the stale equality `s.0 == hi`. `hi` may still appear via
    // its own (harmless) precondition/type-range, but the `Eq(s.0, hi)`
    // connector — which alone lets `hi <= 1000` bound `s.0` — must be gone.
    fn contains_eq_s0_hi(f: &Formula) -> bool {
        let is_s0_hi = |a: &Formula, b: &Formula| {
            matches!((a, b),
                (Formula::Var(x, _), Formula::Var(y, _))
                    if (x == "s.0" && y == "hi") || (x == "hi" && y == "s.0"))
        };
        match f {
            Formula::Eq(a, b) => is_s0_hi(a, b),
            Formula::And(cs) | Formula::Or(cs) => cs.iter().any(contains_eq_s0_hi),
            Formula::Not(inner) => contains_eq_s0_hi(inner),
            _ => false,
        }
    }
    assert!(
        !contains_eq_s0_hi(&overflow_vc.formula),
        "overflow VC must NOT pin post-call `s.0` to entry `hi` via the stale \
         `s.0 == hi`; formula = {:?}",
        overflow_vc.formula
    );
}

#[test]
fn semantic_guard_map_keeps_def_when_terminator_is_goto() {
    // Control: bb0 ends in a plain Goto, so `lo == hi` is live and reaches
    // bb1 — guards the terminator-dest kill against over-dropping.
    let func = term_call_dest_fn(false);
    let map = build_semantic_guard_map(&func);
    let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        defines(&bb1, "lo"),
        "bb1 must retain the live `lo == hi` after a plain Goto; got {bb1:?}"
    );
}

// Trust: regression for the precondition-staleness false-PROVE (e2e probe:
// precond_stale). Models `requires lo <= hi { _ = hi - lo; hi = big; hi - lo }`
// as three blocks: bb0 (first use, hi live), bb1 (reassigns `hi = big`), bb2
// (second `hi - lo` use, downstream of the reassignment). The entry contract
// `lo <= hi` must be dropped at bb1 and bb2 — at bb1 because its own statement
// reassigns `hi`, at bb2 because an ANCESTOR did. The latter is what the
// per-block `v2_live_path_defs` kill cannot see, and is exactly the hole:
// left alive, the stale `lo <= hi` vacuously discharges a real `hi - lo`
// underflow once `hi` has become `big`.
fn precond_reassign_fn(reassign_hi_in_bb1: bool) -> VerifiableFunction {
    let bb1_stmts = if reassign_hi_in_bb1 {
        vec![Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
            span: SourceSpan::default(),
        }]
    } else {
        vec![]
    };
    VerifiableFunction {
        name: "precond_reassign".to_string(),
        def_path: "test::precond_reassign".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("hi".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("lo".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("big".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: bb1_stmts,
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn may_reassigned_propagates_to_descendant_blocks() {
    let func = precond_reassign_fn(true);
    let map = v2_may_reassigned_per_block(&func);
    // bb1's own statement reassigns `hi`.
    assert!(
        map.get(&BlockId(1)).is_some_and(|s| s.contains("hi")),
        "bb1 reassigns `hi`; its may-reassigned set must contain it; got {:?}",
        map.get(&BlockId(1))
    );
    // bb2 is downstream of the reassignment — the ancestor case that the
    // per-block path-def kill misses and the precondition staleness needs.
    assert!(
        map.get(&BlockId(2)).is_some_and(|s| s.contains("hi")),
        "bb2 is downstream of the `hi` reassignment; must inherit it; got {:?}",
        map.get(&BlockId(2))
    );
    // bb0 precedes the reassignment — `hi` is still the entry value there, so
    // the precondition `lo <= hi` must stay live for bb0's first `hi - lo`.
    assert!(
        !map.get(&BlockId(0)).is_some_and(|s| s.contains("hi")),
        "bb0 precedes the reassignment; `hi` must NOT be killed there; got {:?}",
        map.get(&BlockId(0))
    );
}

#[test]
fn may_reassigned_empty_when_no_reassignment() {
    // Control: no block reassigns `hi`, so the precondition stays live
    // everywhere — guards the kill against over-dropping (false-FAILs).
    let func = precond_reassign_fn(false);
    let map = v2_may_reassigned_per_block(&func);
    for b in 0..3 {
        assert!(
            !map.get(&BlockId(b)).is_some_and(|s| s.contains("hi")),
            "no reassignment of `hi`; bb{b} must not kill it; got {:?}",
            map.get(&BlockId(b))
        );
    }
}

// ---------------------------------------------------------------------------
// KILL-ORACLE WRITE-CHANNEL COVERAGE AUDIT (staleness-class S0)
//
// The staleness class is closed iff the redef/kill oracle
// (`v2_may_reassigned_per_block`) drops a fact about a place `x` whenever `x`
// may be mutated on a path to the VC. This audit exercises EVERY MIR
// value-mutation channel against the REAL kill oracle and asserts, per channel,
// whether a fact about `x` is dropped — turning "which channels does the kill
// capture?" from a hand-wave into a computed, regression-locked table.
//
// A channel that is COVERED is hard-asserted (its kill must never regress).
// A channel that is NOT covered is a candidate gap: either a real hole (fix the
// oracle) or sound via a separate fail-closed backstop (documented). Each such
// channel here has been adjudicated end-to-end (see commit history): union
// construction (`AggregateKind::Adt(active_field)`) and custom Drop both
// fail closed elsewhere; a write-only channel (Retag) is not a value mutation.
// ---------------------------------------------------------------------------

/// Build `bb0 { <stmts>; <term> } bb1 { return }` over `locals` (local 1 is the
/// fact-bearing `x`), and return whether the kill oracle DROPS a fact `x == 5`
/// at bb1 — i.e. whether the channel exercised in bb0 is captured.
fn kill_drops_x_fact(
    locals: Vec<LocalDecl>,
    bb0_stmts: Vec<Statement>,
    bb0_term: Terminator,
) -> bool {
    let func = VerifiableFunction {
        name: "chan".into(),
        def_path: "chan".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![
                BasicBlock { id: BlockId(0), stmts: bb0_stmts, terminator: bb0_term },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let kill = v2_may_reassigned_per_block(&func);
    let empty = trust_types::fx::FxHashSet::default();
    let at_bb1 = kill.get(&BlockId(1)).unwrap_or(&empty);
    let fact =
        Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5)));
    !formula_survives_redefs(&fact, at_bb1)
}

fn x_u32() -> LocalDecl {
    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) }
}
fn ret_unit() -> LocalDecl {
    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) }
}
fn assign_x(v: u128) -> Statement {
    Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(v, 32))),
        span: SourceSpan::default(),
    }
}

#[test]
fn kill_oracle_covers_whole_local_store() {
    assert!(
        kill_drops_x_fact(
            vec![ret_unit(), x_u32()],
            vec![assign_x(7)],
            Terminator::Goto(BlockId(1))
        ),
        "channel: whole-local store `x = 7` must be captured"
    );
}

#[test]
fn kill_oracle_covers_set_discriminant() {
    let x = LocalDecl {
        index: 1,
        ty: Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "E".into(),
            fields: vec![("__tag".into(), Ty::i64())],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, },
        name: Some("x".into()),
    };
    assert!(
        kill_drops_x_fact(
            vec![ret_unit(), x],
            vec![Statement::SetDiscriminant { place: Place::local(1), variant_index: 1 }],
            Terminator::Goto(BlockId(1)),
        ),
        "channel: SetDiscriminant on `x` must be captured"
    );
}

#[test]
fn kill_oracle_covers_call_dest_and_mut_arg() {
    // Call writes its dest `x`.
    assert!(
        kill_drops_x_fact(
            vec![ret_unit(), x_u32()],
            vec![],
            Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                func: "f".into(),
                args: vec![],
                dest: Place::local(1),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                is_foreign: false,
            },
        ),
        "channel: Call dest = x must be captured"
    );
    // Call mutates `x` through a `&mut x` argument.
    let r = LocalDecl {
        index: 2,
        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
        name: Some("r".into()),
    };
    assert!(
        kill_drops_x_fact(
            vec![ret_unit(), x_u32(), r],
            vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                span: SourceSpan::default()
            }],
            Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                func: "f".into(),
                args: vec![Operand::Move(Place::local(2))],
                dest: Place::local(0),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                is_foreign: false,
            },
        ),
        "channel: Call(&mut x) must be captured (mutable-borrow havoc)"
    );
}

#[test]
fn kill_oracle_covers_opaque_deref_store_channels() {
    // Reseated &mut: `r=&mut x; r=&mut x; *r=7`.
    let r = LocalDecl {
        index: 2,
        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
        name: Some("r".into()),
    };
    let reseat = vec![
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place { local: 2, projections: vec![Projection::Deref] },
            rvalue: assign_rv(7),
            span: SourceSpan::default(),
        },
    ];
    assert!(
        kill_drops_x_fact(
            vec![ret_unit(), x_u32(), r.clone()],
            reseat,
            Terminator::Goto(BlockId(1))
        ),
        "channel: reseated opaque `*r = v` must be captured (deref-store havoc)"
    );
    // Cast-laundered: `tmp=&mut x; p=tmp as *mut; *p=7`.
    let tmp = LocalDecl {
        index: 2,
        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
        name: Some("tmp".into()),
    };
    let p = LocalDecl {
        index: 3,
        ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) },
        name: Some("p".into()),
    };
    let cast = vec![
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Cast(
                Operand::Copy(Place::local(2)),
                Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) },
            ),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place { local: 3, projections: vec![Projection::Deref] },
            rvalue: assign_rv(7),
            span: SourceSpan::default(),
        },
    ];
    assert!(
        kill_drops_x_fact(
            vec![ret_unit(), x_u32(), tmp, p],
            cast,
            Terminator::Goto(BlockId(1))
        ),
        "channel: cast-laundered `*p = v` must be captured (deref-pointer-is-opaque)"
    );
}

fn assign_rv(v: u128) -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Uint(v, 32)))
}

// AUDIT REPORT: the residual channels. Each is computed against the real kill
// and printed; the assertions encode the ADJUDICATED status so a regression
// (a channel silently flipping coverage) breaks the test.
#[test]
fn kill_oracle_channel_coverage_report() {
    // Deinit{x}: invalidates x's value. Adjudicate whether the kill captures it.
    let deinit = kill_drops_x_fact(
        vec![ret_unit(), x_u32()],
        vec![Statement::Deinit { place: Place::local(1) }],
        Terminator::Goto(BlockId(1)),
    );
    // Drop{x} terminator (custom Drop side effect). Mutation through &mut self
    // requires a prior `&mut x` escape, which the mutable-borrow havoc already
    // captures (adjudicated end-to-end: fails closed). The bare Drop terminator
    // with no prior borrow does not change x's value through a name the kill
    // tracks.
    let drop_term = kill_drops_x_fact(
        vec![ret_unit(), x_u32()],
        vec![],
        Terminator::Drop {
            unwind: UnwindEdge::Unreachable,
            place: Place::local(1),
            target: BlockId(1),
            span: SourceSpan::default(),
        },
    );
    // Opaque terminator (inline asm and other unmodeled control): a conservative
    // sink. Whether the kill havocs across it.
    let opaque = kill_drops_x_fact(
        vec![ret_unit(), x_u32()],
        vec![],
        Terminator::Opaque {
            kind: "asm".into(),
            targets: vec![BlockId(1)],
            span: SourceSpan::default(),
        },
    );
    // Intrinsic mutating through a `&mut x` argument (e.g. copy_nonoverlapping)
    // as a STATEMENT (no Call terminator to trigger the mutable-borrow havoc).
    let r = LocalDecl {
        index: 2,
        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
        name: Some("r".into()),
    };
    let intrinsic = kill_drops_x_fact(
        vec![ret_unit(), x_u32(), r],
        vec![
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                span: SourceSpan::default(),
            },
            Statement::Intrinsic {
                name: "copy_nonoverlapping".into(),
                args: vec![Operand::Move(Place::local(2))],
            },
        ],
        Terminator::Goto(BlockId(1)),
    );
    eprintln!(
        "KILL-CHANNEL-AUDIT deinit={deinit} drop_term={drop_term} opaque={opaque} intrinsic_mut_arg={intrinsic}"
    );
    // Adjudicated states (each `false` is backstopped by a separate fail-closed
    // gate, so no stale-fact false-PROOF results; each `true` is a locked kill):
    //   - deinit (false): `Statement::Deinit` does not appear in current rustc
    //                     MIR (trust-types marks it fail-closed if it ever does).
    //   - drop_term (TRUE, locked — callee-write false-accept sweep): the OLD
    //                     adjudication ("a custom Drop mutates only through
    //                     `&mut self`, whose `&mut x` escape the mutable-borrow
    //                     havoc kills") was DISPROVED by a live lane-level false
    //                     proof: a struct field `&mut u32` written in `Drop`
    //                     (`*self.r = u32::MAX`) mutates a pointee with NO
    //                     `&mut` statement between the guard and the use — the
    //                     borrow was taken BEFORE the guard, and no Call fires.
    //                     `terminator_def_names` now havocs at `Drop` exactly
    //                     like a Call (mut-borrowed + mut-pointer locals + the
    //                     dropped place + its deref-extension).
    //   - opaque/asm (false): with NO mut-borrowed/mut-pointer local there is no
    //                     modeled mutation channel to a bare scalar; inline asm
    //                     itself lowers to `InlineAsm` → `UnsupportedMir` → the
    //                     function is not certified (e2e: asm_out → `[unknown]`).
    //                     (When such locals DO exist, the new `Opaque` havoc arm
    //                     kills them — not visible to this bare-scalar fixture.)
    //   - intrinsic ptr (false): a write through a pointer needs a `&mut x`/
    //                     `&raw mut x` escape (killed) and the raw-pointer op
    //                     fails closed (`hardened_unsafe_operation`).
    // The asserted values are the regression sentinel: a flip to `true` is a
    // precision/soundness gain to lock; a flip whose backstop also weakens is a
    // hole to fix.
    assert!(
        !deinit && drop_term && !opaque && !intrinsic,
        "a residual kill-channel changed coverage; re-adjudicate the backstop \
         before locking: deinit={deinit} drop={drop_term} opaque={opaque} intrinsic={intrinsic}"
    );
}

// ----- S2c item 4: the WRITE-COMPLETENESS LEMMA, compile-checked -----
//
// The closure theorem rests on one lemma: every MIR Statement/Terminator that
// can change a place's value is CAPTURED by the version oracle's write
// detection (`block_written_names`) — so the freshness theorem applies to it.
//
// The classification is `trust_types::{Statement,Terminator}::write_effect()`,
// whose match is EXHAUSTIVE with NO wildcard (it lives in the enum's defining
// crate, where `#[non_exhaustive]` still permits exhaustive matching). So
// adding a new MIR write variant FAILS COMPILATION of trust-types until it is
// classified — a new write channel cannot silently bypass the oracle. This test
// closes the loop: every `Captured` channel is actually captured at runtime.

#[test]
fn write_completeness_lemma_holds_for_captured_channels() {
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody, VerifiableFunction, WriteEffect,
    };
    // For each `Captured` statement channel, block_written_names must actually
    // capture the written name `x` — closing the loop between the compile-time
    // classification (write_effect) and the runtime write detection.
    let probe = |stmt: Statement| -> bool {
        let func = VerifiableFunction {
            name: "wc".into(),
            def_path: "wc".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![stmt],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        // Overlap-aware (the oracle's real semantics): a write to any name
        // overlapping `x` invalidates a fact about `x`.
        super::block_written_names(&func, &func.body.blocks[0])
            .iter()
            .any(|n| super::place_names_overlap(n, "x"))
    };
    // The lemma: a `Captured` statement that writes `x` IS captured by the
    // oracle; a `NoValueWrite` statement is not (an entry fact stays live).
    let assign_x = Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
        span: SourceSpan::default(),
    };
    assert_eq!(assign_x.write_effect(), WriteEffect::Captured);
    assert!(probe(assign_x), "a Captured Assign of `x` must be captured by the oracle");

    // SetDiscriminant is Captured (classification); its runtime name is the
    // discriminant slot, exercised on enums elsewhere — assert the taxonomy.
    let set_disc = Statement::SetDiscriminant { place: Place::local(1), variant_index: 1 };
    assert_eq!(set_disc.write_effect(), WriteEffect::Captured);

    assert_eq!(Statement::Nop.write_effect(), WriteEffect::NoValueWrite);
    assert!(!probe(Statement::Nop), "a NoValueWrite statement must not bump");
    assert_eq!(Statement::StorageDead(1).write_effect(), WriteEffect::NoValueWrite);
    assert!(!probe(Statement::StorageDead(1)));

    // Terminator side: Call is Captured; control-flow is NoValueWrite.
    assert_eq!(
        Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            func: "f".into(),
            args: vec![],
            dest: Place::local(1),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            is_unsafe_sig: false,
            is_foreign: false,
        }
        .write_effect(),
        WriteEffect::Captured
    );
    assert_eq!(Terminator::Return.write_effect(), WriteEffect::NoValueWrite);
}

// =======================================================================
// STALENESS-CLASS S1 — the version oracle + the FRESHNESS THEOREM
//
// The architectural invariant that makes the staleness class *provably*
// closed (not merely tested): name every place by its REACHING DEFINITION, so
// a fact established about `x` at point S and a VC reading `x` at point Q name
// DIFFERENT SMT variables whenever `x` was written between S and Q — making a
// stale fact unable to constrain the VC.
//
// This is a TEST-ONLY oracle: it touches no production VC path. Its job is to
// discharge the theorem as a checkable property over hard cases + the corpus,
// and to prove the oracle is a SOUND replacement for the battle-tested kill.
//
//   reaching-def version of a NAME `n` at block B = the set of "writer ids"
//   that may reach B's entry: -1 = the entry/parameter value, or a block index
//   where `n` was written. Standard forward may-dataflow (monotone union →
//   terminates). The writer set reuses the EXACT gen-set the kill uses
//   (`block_written_names`), so the two analyses are comparable.
//
//   FRESHNESS THEOREM: for every block B and name n,
//       n ∈ may_reassigned[B]  ⟹  version(n, B) ≠ { -1 }
//   i.e. whenever the kill would drop an entry-established fact about n at B,
//   the reaching-def version at B differs from the entry version — so the
//   versioned name is disjoint and the stale fact is unrepresentable. Holds
//   even for LOOPS: at a loop header the back-edge contributes a non-entry
//   writer id, so the header's version is {-1, W} ≠ {-1} (this is why
//   reaching-def-SET versioning closes loops where single-def-point versioning
//   — the variant an earlier adversary refuted — could not).
// =======================================================================

// The version oracle (`block_written_names`, `reaching_def_versions`) was
// promoted to production scope in S2a; the S1 theorem tests consume it via
// `super::`. (`use super::{...}` at the top of this module.)

/// Assert the FRESHNESS THEOREM on `func`: every name the kill drops at a block
/// has a non-entry reaching-def version there (so an entry-established fact is
/// renamed away — unrepresentable). Returns (#kill-drops, #precision-gain): the
/// second counts (block,name) cells where versioning keeps a fact the kill
/// drops would-be... (here, entry-established, so the two agree; precision gain
/// shows up only for non-entry establish points, measured separately).
fn assert_freshness(func: &VerifiableFunction) {
    let kill = v2_may_reassigned_per_block(func);
    let ver = reaching_def_versions(func);
    let entry_only = BTreeSet::from([-1i64]);
    for block in &func.body.blocks {
        let empty = FxHashSet::default();
        let killed = kill.get(&block.id).unwrap_or(&empty);
        let vers = ver.get(&block.id);
        for name in killed {
            let v = vers.and_then(|m| m.get(name));
            assert!(
                v.is_some_and(|s| *s != entry_only),
                "FRESHNESS VIOLATED in `{}` at bb{}: name `{name}` is killed (may-reassigned) \
                 but its reaching-def version is {:?} (== entry) — an entry fact would NOT be \
                 renamed away, re-opening staleness",
                func.name,
                block.id.0,
                v
            );
        }
    }
}

#[test]
fn freshness_theorem_holds_on_acyclic_reassign() {
    // bb0: hi = big; goto bb1 — `hi` killed at bb1, version must differ.
    assert_freshness(&sem_stale_blockdef_fn(true));
}

#[test]
fn freshness_theorem_holds_on_reseated_deref_store() {
    assert_freshness(&sem_reseat_havoc_fn(true));
}

#[test]
fn freshness_theorem_holds_on_loop_carried_counter() {
    // The hard case: bb0 i=0; bb1 (header) switch; bb2 (body) i=i+1; back-edge
    // to bb1. `i` is loop-carried — single-def-point versioning fails here, but
    // reaching-def-SET versioning gives the header version {-1, bb2} ≠ {-1}.
    use trust_types::{
        BinOp, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody, VerifiableFunction,
    };
    let func = VerifiableFunction {
        name: "loop_counter".into(),
        def_path: "loop_counter".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("i".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("c".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // header: c = i < n; switch(c) { 0 => bb3 (exit), _ => bb2 (body) }
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        exhaustive_enum_unreachable: false,
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                // body: i = i + 1; back-edge to header
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    // `i` is killed at the header (back-edge) — freshness must give it a
    // non-entry version there, proving the loop case is closeable by versioning.
    let ver = reaching_def_versions(&func);
    let i_at_header = ver.get(&BlockId(1)).and_then(|m| m.get("i")).cloned();
    // Header version of `i` = {bb0 (preheader `i=0`), bb2 (back-edge `i=i+1`)}:
    // the back-edge writer (bb2) is present and the set has ≥2 elements, so the
    // header's `i` is a DISTINCT version from any single-iteration value — the
    // reaching-def SET distinguishes iterations, which a single-def-point scheme
    // cannot. (This is the loop case an earlier adversary said versioning
    // couldn't close; reaching-def-SET versioning closes it.)
    assert!(
        i_at_header.as_ref().is_some_and(|s| s.contains(&2) && s.len() >= 2),
        "loop header version of `i` must include the back-edge writer (bb2) and join \
         ≥2 reaching defs, distinguishing iterations: got {i_at_header:?}"
    );
    assert_freshness(&func);
}

#[test]
fn freshness_theorem_holds_on_corpus() {
    // Run the theorem over every hand-built fixture in this module that has a
    // reassignment — the corpus of staleness shapes accumulated this session.
    assert_freshness(&sem_stale_blockdef_fn(true));
    assert_freshness(&sem_stale_blockdef_fn(false));
    assert_freshness(&sem_reseat_havoc_fn(true));
    assert_freshness(&sem_reseat_havoc_fn(false));
    assert_freshness(&precond_reassign_fn(true));
    assert_freshness(&precond_reassign_fn(false));
}

/// Build a `k`-block chain bb0→…→bb(k-1)→Return where each block in
/// `write_blocks` does `x = <const>`, with an optional back-edge `from→to`
/// (a loop). `x` is local 1. Used to fuzz freshness/parity over many CFG shapes.
fn chain_fn(
    k: usize,
    write_blocks: &[usize],
    back_edge: Option<(usize, usize)>,
) -> VerifiableFunction {
    use trust_types::{
        ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty,
        VerifiableBody, VerifiableFunction,
    };
    let mut blocks = Vec::new();
    for b in 0..k {
        let stmts = if write_blocks.contains(&b) {
            vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint((b as u128) + 1, 32))),
                span: SourceSpan::default(),
            }]
        } else {
            vec![]
        };
        let term = if let Some((from, to)) = back_edge {
            if b == from {
                // diamond at the back-edge source: branch to `to` (loop) or fall through.
                Terminator::SwitchInt {
                    exhaustive_enum_unreachable: false,
                    discr: Operand::Copy(Place::local(1)),
                    targets: vec![(0, BlockId(to))],
                    otherwise: BlockId(if b + 1 < k { b + 1 } else { b }),
                    span: SourceSpan::default(),
                }
            } else if b + 1 < k {
                Terminator::Goto(BlockId(b + 1))
            } else {
                Terminator::Return
            }
        } else if b + 1 < k {
            Terminator::Goto(BlockId(b + 1))
        } else {
            Terminator::Return
        };
        blocks.push(BasicBlock { id: BlockId(b), stmts, terminator: term });
    }
    VerifiableFunction {
        name: format!("chain_{k}"),
        def_path: "chain".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks,
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
fn freshness_and_parity_hold_on_generated_battery() {
    // Exhaustively enumerate small CFG shapes × write patterns × back-edges and
    // assert BOTH the freshness theorem and version⟺kill parity on every one —
    // turning "holds on a few hand-built cases" into broad, deterministic
    // evidence that reaching-def versioning is a sound, kill-equivalent oracle.
    let entry_only = BTreeSet::from([-1i64]);
    let mut checked = 0usize;
    for k in 2..=5usize {
        // every subset of blocks that write x
        for mask in 0u32..(1u32 << k) {
            let writes: Vec<usize> = (0..k).filter(|b| mask & (1 << b) != 0).collect();
            // no back-edge, plus a few loop shapes
            let mut edges: Vec<Option<(usize, usize)>> = vec![None];
            if k >= 3 {
                edges.push(Some((k - 1, 1)));
                edges.push(Some((k - 1, 0)));
            }
            for be in &edges {
                let func = chain_fn(k, &writes, *be);
                assert_freshness(&func);
                // parity: version-stale ⟺ killed, every (block, name)
                let kill = v2_may_reassigned_per_block(&func);
                let ver = reaching_def_versions(&func);
                for block in &func.body.blocks {
                    let empty = FxHashSet::default();
                    let killed = kill.get(&block.id).unwrap_or(&empty);
                    if let Some(vmap) = ver.get(&block.id) {
                        for (name, vset) in vmap {
                            assert_eq!(
                                killed.contains(name),
                                *vset != entry_only,
                                "parity break: k={k} writes={writes:?} be={be:?} bb{} name={name}",
                                block.id.0
                            );
                        }
                    }
                }
                checked += 1;
            }
        }
    }
    eprintln!(
        "FRESHNESS-BATTERY checked {checked} (CFG-shape × write-pattern × back-edge) cases"
    );
    assert!(checked >= 150, "battery too small: {checked}");
}

#[test]
fn versioning_is_a_sound_replacement_for_the_kill() {
    // The PARITY theorem (entry-established facts): versioning marks a name
    // stale at B (version ≠ {-1}) IFF the kill drops it (name ∈ may_reassigned).
    // Agreement ⟹ versioning never KEEPS a fact the kill drops (sound) and
    // never DROPS one the kill keeps at the entry-establish point (no precision
    // loss vs the kill). Divergence either way is a finding.
    let entry_only = BTreeSet::from([-1i64]);
    for func in
        [sem_stale_blockdef_fn(true), sem_reseat_havoc_fn(true), precond_reassign_fn(true)]
    {
        let kill = v2_may_reassigned_per_block(&func);
        let ver = reaching_def_versions(&func);
        for block in &func.body.blocks {
            let empty = FxHashSet::default();
            let killed = kill.get(&block.id).unwrap_or(&empty);
            let vers = ver.get(&block.id);
            let all_names: FxHashSet<String> =
                vers.map(|m| m.keys().cloned().collect()).unwrap_or_default();
            for name in &all_names {
                let killed_here = killed.contains(name);
                let stale_by_version =
                    vers.and_then(|m| m.get(name)).is_some_and(|s| *s != entry_only);
                assert_eq!(
                    killed_here, stale_by_version,
                    "kill/version DISAGREE on `{name}` in `{}` bb{}: kill={killed_here} \
                     version-stale={stale_by_version}",
                    func.name, block.id.0
                );
            }
        }
    }
}

// ----- S2a: production shadow-parity audit -----

#[test]
fn shadow_parity_holds_on_whole_name_corpus() {
    // The production shadow audit (overlap-based, terminator-exempt) must report
    // ZERO disagreements on every whole-name fixture — versioning is drop-
    // equivalent to the kill there. This is the at-scale parity the naming flip
    // relies on, now runnable in production on any real function.
    for func in [
        sem_stale_blockdef_fn(true),
        sem_stale_blockdef_fn(false),
        sem_reseat_havoc_fn(true),
        precond_reassign_fn(true),
        chain_fn(4, &[1, 3], Some((3, 1))),
        chain_fn(5, &[0, 2, 4], None),
    ] {
        assert_eq!(
            shadow_parity_disagreements(&func),
            0,
            "shadow parity must agree with the kill on `{}`",
            func.name
        );
    }
}

#[test]
fn shadow_parity_holds_across_generated_battery() {
    let mut total = 0usize;
    for k in 2..=5usize {
        for mask in 0u32..(1u32 << k) {
            let writes: Vec<usize> = (0..k).filter(|b| mask & (1 << b) != 0).collect();
            let edges: Vec<Option<(usize, usize)>> = if k >= 3 {
                vec![None, Some((k - 1, 1)), Some((k - 1, 0))]
            } else {
                vec![None]
            };
            for be in edges {
                assert_eq!(
                    shadow_parity_disagreements(&chain_fn(k, &writes, be)),
                    0,
                    "battery parity break: k={k} writes={writes:?} be={be:?}"
                );
                total += 1;
            }
        }
    }
    eprintln!("SHADOW-PARITY-BATTERY {total} functions, 0 disagreements");
    assert!(total >= 150);
}

#[test]
fn version_token_is_none_for_unwritten_and_some_after_write() {
    // bb0 writes x; bb1 does not. Token absent at entry-only, present after write.
    let func = sem_stale_blockdef_fn(true); // writes `lo` in bb0 (lo=hi) and bb1
    let vctx = VersionCtx::build(&func);
    // `hi` is a never-written parameter → unversioned (None) everywhere.
    assert!(
        vctx.version_token(BlockId(0), "hi").is_none(),
        "a never-written name must stay unversioned (byte-identical on flip)"
    );
    // `lo` is written → has a token at the block that writes it.
    assert!(
        vctx.version_token(BlockId(0), "lo").is_some(),
        "a written name must carry a version token"
    );
}

// S2b: the projection-overlap gap the S2a audit surfaced is now CLOSED by the
// overlap-aware query `is_versioned_query`. A write to WHOLE `s` must
// version-stale a fact about the descendant `s.0` (the kill drops it via
// place_names_overlap), and a write to `s.0` must version-stale a fact about
// whole `s`. Both directions are asserted drop-equivalent to the kill.
#[test]
fn overlap_aware_query_closes_projection_gap() {
    use trust_types::{
        ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody, VerifiableFunction,
    };
    // bb0 writes WHOLE `s`; bb1 is the successor where a fact about `s.0` lands.
    let write_whole_s = |proj: Vec<Projection>| VerifiableFunction {
        name: "proj".into(),
        def_path: "proj".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Tuple(vec![Ty::u32(), Ty::u32()]),
                    name: Some("s".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place { local: 1, projections: proj },
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    // Whole-`s` write: a fact about `s.0` must be version-stale at bb1.
    let whole = write_whole_s(vec![]);
    let v = VersionCtx::build(&whole);
    assert!(
        v.is_versioned_query(BlockId(1), "s.0"),
        "a write to whole `s` must version-stale a fact about descendant `s.0`"
    );
    assert!(
        v.is_versioned_query(BlockId(1), "s"),
        "a write to whole `s` must version-stale a fact about `s` itself"
    );
    assert_eq!(shadow_parity_disagreements_overlap(&whole), 0, "whole-s overlap parity");

    // `s.0` write: a fact about ancestor `s` must be version-stale at bb1.
    let field = write_whole_s(vec![Projection::Field(0)]);
    let vf = VersionCtx::build(&field);
    assert!(
        vf.is_versioned_query(BlockId(1), "s"),
        "a write to `s.0` must version-stale a fact about ancestor `s` (overlap)"
    );
    assert_eq!(shadow_parity_disagreements_overlap(&field), 0, "field overlap parity");
}

// ----- S2c Stage 0: statement-granular oracle + the block-level blind spot -----

/// `bb0: y = x + 5 (reads x) ; x = 4e9 ; return`. A read of `x` at stmt0 sees
/// the ENTRY value (x is written LATER, at stmt1). The block-level oracle is
/// blind to ordering — it reports `x` versioned everywhere (because x is
/// written somewhere in the block) — which would rename the stmt0 read apart
/// from an entry fact (a false-FAIL). The statement-granular oracle gets it
/// right: `x` is unversioned (None) at stmt0, versioned only AFTER stmt1.
fn read_before_same_block_write() -> trust_types::VerifiableFunction {
    use trust_types::{
        BinOp, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody, VerifiableFunction,
    };
    VerifiableFunction {
        name: "read_before_write".into(),
        def_path: "read_before_write".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    // stmt0: y = x + 5  (READS x — the entry value)
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(5, 32)),
                        ),
                        span: SourceSpan::default(),
                    },
                    // stmt1: x = 4e9  (WRITES x — AFTER the read)
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(
                            4_000_000_000,
                            32,
                        ))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
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
fn block_level_oracle_is_blind_to_intra_block_order() {
    let func = read_before_same_block_write();
    // BLOCK-level oracle: `x` is written in bb0 (stmt1) so it is versioned —
    // with NO way to express "but not yet, at stmt0". This is the blind spot.
    let block = VersionCtx::build(&func);
    assert!(
        block.version_token(BlockId(0), "x").is_some(),
        "block-level oracle conflates: it reports `x` versioned for the WHOLE block"
    );
}

#[test]
fn stmt_oracle_distinguishes_read_before_and_after_write() {
    let func = read_before_same_block_write();
    let sv = StmtVersionCtx::build(&func);
    // At stmt0 (the read of `x`), `x` has NOT been written yet → entry value →
    // unversioned. This is what makes an entry fact about `x` still apply.
    assert!(
        sv.version_token_at(&func, BlockId(0), 0, "x").is_none(),
        "a read BEFORE the same-block write must see the unversioned entry value of `x`"
    );
    // After stmt1 (the write), `x` is versioned — distinct from the entry value.
    assert!(
        sv.version_token_at(&func, BlockId(0), 2, "x").is_some(),
        "after the same-block write, `x` must be versioned"
    );
    // The staleness verdict matches: not stale at stmt0, stale after stmt1.
    assert!(!sv.is_versioned_stale_at(&func, BlockId(0), 0, "x"));
    assert!(sv.is_versioned_stale_at(&func, BlockId(0), 2, "x"));
}

/// A multi-write-per-block, mid-block-VC battery — the shape the BLOCK-level
/// parity audit is blind to. Each function has a block with several writes and
/// reads interleaved.
fn intra_block_battery() -> Vec<trust_types::VerifiableFunction> {
    use trust_types::{
        BinOp, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody, VerifiableFunction,
    };
    let mk = |stmts: Vec<Statement>| VerifiableFunction {
        name: "intra".into(),
        def_path: "intra".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("z".into()) },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let asn = |l: usize, v: u128| Statement::Assign {
        place: Place::local(l),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(v, 32))),
        span: SourceSpan::default(),
    };
    let add = |l: usize, a: usize, b: usize| Statement::Assign {
        place: Place::local(l),
        rvalue: Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(a)),
            Operand::Copy(Place::local(b)),
        ),
        span: SourceSpan::default(),
    };
    vec![
        mk(vec![add(2, 1, 1), asn(1, 4_000_000_000)]), // read x, then write x
        mk(vec![asn(1, 7), add(2, 1, 1)]),             // write x, then read x
        mk(vec![add(2, 1, 1), asn(1, 9), add(3, 1, 1)]), // read, write, read
        mk(vec![asn(1, 1), asn(1, 2), add(2, 1, 1)]),  // two writes, read
        mk(vec![add(3, 1, 1), asn(2, 5), add(3, 2, 1)]), // interleaved x/y
    ]
}

#[test]
fn flip_is_verdict_equivalent_to_kill_statement_granular() {
    // THE SOUNDNESS WITNESS: the flip's "does an entry fact apply at (B,i)?"
    // verdict equals the statement-granular kill's drop verdict — on the corpus,
    // the generated battery, AND the intra-block battery the block-level audit
    // cannot witness. 0 disagreements ⟹ the flip is a sound, drop-equivalent
    // replacement for the kill at the correct granularity.
    let mut total = 0usize;
    let corpus = vec![
        sem_stale_blockdef_fn(true),
        sem_reseat_havoc_fn(true),
        precond_reassign_fn(true),
        read_before_same_block_write(),
    ];
    for func in corpus.into_iter().chain(intra_block_battery()) {
        assert_eq!(
            flip_matches_kill_stmt(&func),
            0,
            "flip/kill statement-granular disagreement on `{}`",
            func.name
        );
        total += 1;
    }
    for k in 2..=5usize {
        for mask in 0u32..(1u32 << k) {
            let writes: Vec<usize> = (0..k).filter(|b| mask & (1 << b) != 0).collect();
            let edges: Vec<Option<(usize, usize)>> =
                if k >= 3 { vec![None, Some((k - 1, 1))] } else { vec![None] };
            for be in edges {
                assert_eq!(flip_matches_kill_stmt(&chain_fn(k, &writes, be)), 0);
                total += 1;
            }
        }
    }
    eprintln!("FLIP-WITNESS {total} functions, 0 statement-granular disagreements");
    assert!(total >= 100);
}

#[test]
fn flip_token_distinctness_holds_on_corpus_and_battery() {
    // P-C witness: two read points straddling a write get DISTINCT tokens, so a
    // fact at the earlier point cannot unify with the body at the later point.
    // 0 violations across the corpus + battery (this would FAIL before the P-A
    // oracle fix, which is why the original witness's blind spot mattered).
    let mut total = 0usize;
    for func in [
        sem_stale_blockdef_fn(true),
        sem_reseat_havoc_fn(true),
        precond_reassign_fn(true),
        read_before_same_block_write(),
    ]
    .into_iter()
    .chain(intra_block_battery())
    {
        assert_eq!(
            flip_token_distinctness_violations(&func),
            0,
            "token-distinctness violated on `{}`",
            func.name
        );
        total += 1;
    }
    for k in 2..=5usize {
        for mask in 0u32..(1u32 << k) {
            let writes: Vec<usize> = (0..k).filter(|b| mask & (1 << b) != 0).collect();
            assert_eq!(flip_token_distinctness_violations(&chain_fn(k, &writes, None)), 0);
            total += 1;
        }
    }
    assert!(total >= 50);
}

#[test]
fn block_def_establish_versioning_subsumes_havoc_kill() {
    // WITNESS for deleting `drop_havoced_block_defs`: across the staleness
    // corpus (incl. the opaque-deref-store havoc shapes the kill exists for)
    // and the generated battery, the establish-point versioning leaves NO
    // residual — every block-def whose subject is havoced is either pinned to
    // an establish point distinct from the terminal body (stale → disconnected)
    // or correctly kept (fresh/RHS-only). 0 residual ⟹ the kill is redundant.
    let mut total = 0usize;
    let mut residual = 0usize;
    for func in [
        sem_stale_blockdef_fn(true),
        sem_reseat_havoc_fn(true),
        precond_reassign_fn(true),
        read_before_same_block_write(),
    ]
    .into_iter()
    .chain(intra_block_battery())
    {
        residual += block_def_establish_subsumes_kill(&func);
        total += 1;
    }
    for k in 2..=5usize {
        for mask in 0u32..(1u32 << k) {
            let writes: Vec<usize> = (0..k).filter(|b| mask & (1 << b) != 0).collect();
            residual += block_def_establish_subsumes_kill(&chain_fn(k, &writes, None));
            total += 1;
        }
    }
    assert_eq!(
        residual, 0,
        "establish-point versioning leaves {residual} havoced-subject defs the \
         kill is still load-bearing for (across {total} functions)"
    );
    assert!(total >= 50);
}

#[test]
fn version_rename_at_distinguishes_straddled_reads() {
    // `y = x + 5 ; x = big`: a VC body `x + 5` read at stmt0 renames to bare `x`
    // (entry value); the SAME `x + 5` evaluated at stmt2 (after the write) renames
    // to `x#...`. The two are DIFFERENT formulas → a stale fact about the entry
    // `x` constrains the stmt0 read but NOT the post-write read.
    use trust_types::Sort;
    let func = read_before_same_block_write();
    let sv = StmtVersionCtx::build(&func);
    let body =
        Formula::Add(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5)));
    let at0 = version_rename_at(&body, &sv, &func, BlockId(0), 0);
    let at2 = version_rename_at(&body, &sv, &func, BlockId(0), 2);
    assert!(
        at0.free_variables().contains("x"),
        "read at stmt0 keeps the unversioned entry `x`: {at0:?}"
    );
    assert!(
        !at2.free_variables().contains("x")
            && at2.free_variables().iter().any(|v| v.starts_with("x#")),
        "read at stmt2 (after the write) renames `x` to a versioned name: {at2:?}"
    );
}

#[test]
fn pa_two_same_block_writes_get_distinct_tokens() {
    // P-A regression: `x = 1; x = 2` — the read points after each write must get
    // DISTINCT version tokens (else two intermediate values collapse, defeating
    // the statement-granular oracle the block-def/guard kills will rely on).
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };
    let asn = |v: u128| Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(v, 32))),
        span: SourceSpan::default(),
    };
    let func = VerifiableFunction {
        name: "tc".into(),
        def_path: "tc".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![asn(1), asn(2)],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let sv = StmtVersionCtx::build(&func);
    let t1 = sv.version_token_at(&func, BlockId(0), 1, "x");
    let t2 = sv.version_token_at(&func, BlockId(0), 2, "x");
    assert!(
        t1.is_some() && t2.is_some() && t1 != t2,
        "two same-block writes must yield DISTINCT tokens; got {t1:?} vs {t2:?}"
    );
}

#[test]
fn stmt_oracle_versions_after_a_prior_write() {
    // `x = 7 ; y = x + 5` — here the write PRECEDES the read, so at the read
    // point `x` IS versioned (the entry value is dead). Mirror of the blind-spot
    // case, confirming the oracle is order-sensitive in both directions.
    use trust_types::{
        BinOp, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody, VerifiableFunction,
    };
    let func = VerifiableFunction {
        name: "write_before_read".into(),
        def_path: "write_before_read".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(5, 32)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let sv = StmtVersionCtx::build(&func);
    // The read at stmt1 is AFTER the write at stmt0 → `x` is versioned there.
    assert!(
        sv.version_token_at(&func, BlockId(0), 1, "x").is_some(),
        "a read AFTER a same-block write must see the versioned (non-entry) value"
    );
    // At stmt0 (before the write), still the entry value.
    assert!(sv.version_token_at(&func, BlockId(0), 0, "x").is_none());
}

#[test]
fn overlap_parity_holds_on_corpus_and_battery() {
    // The OVERLAP-AWARE audit (projected probes included) must report ZERO
    // disagreements across the corpus + the generated battery — versioning is
    // drop-equivalent to the kill for projected facts too.
    for func in
        [sem_stale_blockdef_fn(true), sem_reseat_havoc_fn(true), precond_reassign_fn(true)]
    {
        assert_eq!(
            shadow_parity_disagreements_overlap(&func),
            0,
            "overlap parity on `{}`",
            func.name
        );
    }
    let mut total = 0usize;
    for k in 2..=5usize {
        for mask in 0u32..(1u32 << k) {
            let writes: Vec<usize> = (0..k).filter(|b| mask & (1 << b) != 0).collect();
            let edges: Vec<Option<(usize, usize)>> =
                if k >= 3 { vec![None, Some((k - 1, 1))] } else { vec![None] };
            for be in edges {
                assert_eq!(shadow_parity_disagreements_overlap(&chain_fn(k, &writes, be)), 0);
                total += 1;
            }
        }
    }
    assert!(total >= 100, "battery too small: {total}");
}

// =========================================================================
// P0 (2026-08-01) — THE VERSION ORACLE AT THE EXACT LAYER THE BUG LIVES IN.
//
// `stmt_writes_name` answers "does statement k ITSELF write `name`", and
// `StmtVersionCtx::version_token_at` uses it to pick WHICH statement stamps a
// name's version token. Its opaque-deref branch consulted the block-level
// `deref_store_havoc_names`, a whole-function list of BASE LOCAL names — a `&mut`
// parameter contributes the bare `self` — and `place_names_overlap` treats `*` as
// a projection separator, so `place_names_overlap("self", "self*.0")` is TRUE.
// A store to `(*self).1` was therefore reported as a write of its own SIBLING
// `(*self).0`, moving that field's token to the wrong statement and severing it
// from the exact-token out-parameter pin. Downstream, the postcondition read a
// FREE variable and the solver minted a verified counterexample against correct
// code.
//
// These assert the ORACLE directly, so a regression is caught here rather than as
// a mysterious contract-lane verdict.
// =========================================================================

/// `fn d(&mut self) { (*self).0 = 0; (*self).1 = 0; }` with `self: &mut S`, `S`
/// carrying the real rustc-derived `AdtKind` (`None` = un-migrated/unknown).
fn two_field_store_fn(kind: Option<trust_types::AdtKind>) -> VerifiableFunction {
    let adt = match Ty::adt("S", vec![("n".into(), Ty::u64()), ("m".into(), Ty::u64())]) {
        Ty::Adt {
            name,
            fields,
            variants,
            disc_index_safe,
            faithful_enum_repr,
            layout,
            enum_layout,
            ..
        } => Ty::Adt {
            name,
            fields,
            variants,
            disc_index_safe,
            faithful_enum_repr,
            layout,
            enum_layout,
            adt_kind: kind,
        },
        other => other,
    };
    let store = |field: usize, v: u128| Statement::Assign {
        place: Place { local: 1, projections: vec![Projection::Deref, Projection::Field(field)] },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(v, 64))),
        span: SourceSpan::default(),
    };
    VerifiableFunction {
        name: "d".into(),
        def_path: "d".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![]), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(adt) },
                    name: Some("self".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![store(0, 0), store(1, 0)],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Tuple(vec![]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// THE ORACLE-LEVEL ASSERTION THE P0 DEFECT VIOLATED. Each field must carry the
/// token of the statement that ACTUALLY wrote it — `s0_0` for field 0, `s0_1` for
/// field 1. Pre-fix BOTH came back `s0_1`.
#[test]
fn sibling_field_store_does_not_version_its_neighbour() {
    let f = two_field_store_fn(Some(trust_types::AdtKind::Struct));
    let bb = &f.body.blocks[0];

    assert!(
        stmt_writes_name(&f, bb, 0, "self*.0"),
        "statement 0 writes field 0 — the exact-place branch"
    );
    assert!(
        !stmt_writes_name(&f, bb, 1, "self*.0"),
        "statement 1 stores the SIBLING field 1 and CANNOT write field 0; \
         reporting it as a write is the P0 defect"
    );
    assert!(stmt_writes_name(&f, bb, 1, "self*.1"), "statement 1 writes field 1");

    // Ancestors and the whole pointee must STILL report written — the exclusion
    // only removes SIBLING-disjoint paths, never the containing value.
    assert!(stmt_writes_name(&f, bb, 1, "self*"), "the whole pointee is still written");
    assert!(stmt_writes_name(&f, bb, 1, "self"), "the base local is still written");
    assert!(
        stmt_writes_name(&f, bb, 1, "self*.1.0"),
        "a DESCENDANT of the written place is still written"
    );

    let sv = StmtVersionCtx::build(&f);
    let at_end = bb.stmts.len();
    assert_eq!(
        sv.version_token_at(&f, BlockId(0), at_end, "self*.0").as_deref(),
        Some("s0_0"),
        "field 0's post-state is established by statement 0, not by its sibling's store"
    );
    assert_eq!(
        sv.version_token_at(&f, BlockId(0), at_end, "self*.1").as_deref(),
        Some("s0_1"),
        "field 1's post-state is established by statement 1"
    );
}

/// FAIL-CLOSED, UNION. Union fields OVERLAP at byte offset 0, so a store to field
/// 1 genuinely CAN change field 0. The oracle must keep the whole-pointee havoc —
/// this is the direct soundness witness that the precision fix is gated, not
/// blanket. (`AdtKind::Union` is stamped by `trust-mir-extract::ty_convert` from
/// rustc's `AdtDef::is_union`.)
#[test]
fn union_sibling_store_still_versions_its_neighbour() {
    let f = two_field_store_fn(Some(trust_types::AdtKind::Union));
    let bb = &f.body.blocks[0];
    assert!(
        stmt_writes_name(&f, bb, 1, "self*.0"),
        "a UNION's fields overlap; the store to field 1 MUST still havoc field 0"
    );
    let sv = StmtVersionCtx::build(&f);
    assert_eq!(
        sv.version_token_at(&f, BlockId(0), bb.stmts.len(), "self*.0").as_deref(),
        Some("s0_1"),
        "a union field read must stay versioned at the LAST overlapping store"
    );
}

/// FAIL-CLOSED, UN-MIGRATED ADT. `adt_kind: None` means the kind was never read
/// from a rustc `AdtDef`. Unknown is not struct: keep the conservative havoc.
#[test]
fn unkinded_adt_sibling_store_still_versions_its_neighbour() {
    let f = two_field_store_fn(None);
    let bb = &f.body.blocks[0];
    assert!(
        stmt_writes_name(&f, bb, 1, "self*.0"),
        "an ADT of unconfirmed kind must keep the whole-pointee havoc"
    );
}

/// CROSS-POINTER ALIASING IS PRESERVED — the property the out-parameter pin's
/// soundness argument rests on ("ALIASING IS NOT ASSUMED AWAY", contract_vcs.rs).
/// A store through `q` must still havoc every name under a DIFFERENT pointer `p`,
/// because the two may denote the same object. Only the storing pointer's OWN
/// tree is subtracted.
#[test]
fn store_through_one_pointer_still_havocs_another() {
    let adt = Ty::adt("S", vec![("n".into(), Ty::u64())]);
    let mut f = two_field_store_fn(Some(trust_types::AdtKind::Struct));
    f.body.locals.push(LocalDecl {
        index: 2,
        ty: Ty::Ref { mutable: true, inner: Box::new(adt) },
        name: Some("q".into()),
    });
    f.body.arg_count = 2;
    // Statement 1 now stores through `q`, not through `self`.
    f.body.blocks[0].stmts[1] = Statement::Assign {
        place: Place { local: 2, projections: vec![Projection::Deref, Projection::Field(0)] },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64))),
        span: SourceSpan::default(),
    };
    let bb = &f.body.blocks[0];
    assert!(
        stmt_writes_name(&f, bb, 1, "self*.0"),
        "a store through `q` may alias `self`'s pointee and MUST still havoc it; \
         subtracting anything but the STORING pointer's own tree would be unsound"
    );
}
