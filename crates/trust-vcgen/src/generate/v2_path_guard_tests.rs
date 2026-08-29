use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
};

use super::{PathGuardCollapse, ReachSummary, generate_v2_safety_vcs, v2_analyze_path_guards};

fn joined_unreachable_from_infeasible_and_feasible_paths() -> VerifiableFunction {
    VerifiableFunction {
        name: "classify".to_string(),
        def_path: "classify".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("_3".into()) },
                LocalDecl { index: 4, ty: Ty::Never, name: Some("_4".into()) },
                LocalDecl { index: 5, ty: Ty::Unit, name: Some("_5".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(5))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                        func: "core::panicking::unreachable_display".to_string(),
                        args: vec![],
                        dest: Place::local(4),
                        target: None,
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Constant(ConstValue::Uint(1, 32)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(2)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(100, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn v2_unreachable_join_uses_disjunctive_path_guards() {
    let func = joined_unreachable_from_infeasible_and_feasible_paths();
    let vcs = generate_v2_safety_vcs(&func);
    let unreach = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Unreachable))
        .expect("expected unreachable VC");

    assert!(
        formula_contains_or(&unreach.formula),
        "join block must keep all incoming path guards, got {:?}",
        unreach.formula
    );
}

/// True if `formula` contains `Ge(Var(var), Int(bound))` anywhere.
fn formula_has_ge_var_int(formula: &Formula, var: &str, bound: i128) -> bool {
    let mut found = false;
    formula.visit(&mut |sub| {
        // Base-name compare: the S2c flip versions the shift amount (`_6` →
        // `_6#s5_0`); the `>= 128` bound is the same semantic obligation.
        if let Formula::Ge(l, r) = sub
            && matches!(l.as_ref(), Formula::Var(n, _) if n.split('#').next() == Some(var))
            && matches!(r.as_ref(), Formula::Int(b) if *b == bound)
        {
            found = true;
        }
    });
    found
}

/// Regression: a `1i128 << (width-1)` shift guarded by `width >= 1 && width <=
/// 127` (`signed_max`/`signed_min`) is provably safe (`width-1 <= 126 < 128`).
/// The VC is built from the SHIFT-LEFT ASSERT terminator (which passes the
/// ASSERT block, not the shift block, and `stmt_index = None`), so the shifted
/// value `1i128`'s width was mis-recovered as the fabricated i64 width (64),
/// yielding the false-FAILing bound `_6 >= 64` (SAT: `_6 = 99 < 128`). The fix
/// recovers the true 128-bit shift-result width from the shift statement's
/// destination, giving `_6 >= 128` (UNSAT under `_6 = width-1 <= 126`).
#[test]
fn signed_max_guarded_i128_shift_uses_result_width_128() {
    use trust_types::VcKind;
    let func = signed_max_fixture();
    let vcs = generate_v2_safety_vcs(&func);
    let shift = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. }))
        .expect("expected ShiftOverflow VC for the `1i128 << (width-1)` shift");

    // The corrected `amount >= width` bound must use the i128 result width 128,
    // never the fabricated-i64 width 64. With the threaded guard `_6 == width-1`
    // and `width <= 127`, `_6 >= 128` is UNSAT (provable) while `_6 >= 64` is SAT
    // (the false-FAIL).
    assert!(
        formula_has_ge_var_int(&shift.formula, "_6", 128),
        "shift overflow bound must be `_6 >= 128` (i128 result width); got {:?}",
        shift.formula
    );
    assert!(
        !formula_has_ge_var_int(&shift.formula, "_6", 64),
        "shift overflow bound must NOT be the fabricated-i64 width `_6 >= 64`; got {:?}",
        shift.formula
    );

    // The guard fact `width <= 127` must reach the VC (proving the bound is
    // actually dischargeable, not merely tightened).
    let mentions_127 = {
        let mut found = false;
        shift.formula.visit(&mut |sub| {
            if let Formula::Le(l, r) = sub
                && matches!(l.as_ref(), Formula::Var(n, _) if n == "width")
                && matches!(r.as_ref(), Formula::Int(127))
            {
                found = true;
            }
        });
        found
    };
    assert!(mentions_127, "guard `width <= 127` must reach the shift VC; got {:?}", shift.formula);
}

/// ADVERSARIAL guardrail: a genuinely-unbounded shift `1i128 << n` (no guard on
/// `n`) must STILL produce a refutable bound — the fix must not inject any
/// `<= 127`-style fact for an unguarded shift. Here the i128 result width is 128,
/// so the bound is `n >= 128`, which is SATISFIABLE (e.g. `n = 200`): a real UB
/// shift correctly refutes. (Pre-fix this used width 64 → `n >= 64`, still SAT;
/// the point is the fix preserves refutability with the corrected width and adds
/// no spurious upper bound on `n`.)
#[test]
fn unguarded_i128_shift_remains_refutable() {
    use trust_types::VcKind;
    // fn g(n: u32) -> i128 { 1i128 << n }
    // bb0: _2 = Lt(n, 128); assert(_2, shl) -> bb1
    // bb1: _0 = Shl(1i128, n); return
    let func = VerifiableFunction {
        name: "g".to_string(),
        def_path: "g".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(128, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::local(2)),
                        expected: true,
                        msg: trust_types::AssertMessage::Overflow(BinOp::Shl),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Shl,
                            Operand::Constant(ConstValue::Int(1)),
                            Operand::Move(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i128(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_v2_safety_vcs(&func);
    let shift = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. }))
        .expect("expected ShiftOverflow VC for the unguarded `1i128 << n`");

    // Corrected width: bound is `n >= 128`, refutable (no guard bounds n).
    assert!(
        formula_has_ge_var_int(&shift.formula, "n", 128),
        "unguarded shift bound must be `n >= 128` (i128 result width); got {:?}",
        shift.formula
    );
    // No `<= 127`-style upper bound on `n` may be injected — the shift is
    // unguarded, so `n` must stay free above 128 (the violation stays SAT).
    let injects_127_on_n = {
        let mut found = false;
        shift.formula.visit(&mut |sub| {
            if let Formula::Le(l, r) = sub
                && matches!(l.as_ref(), Formula::Var(name, _) if name == "n")
                && matches!(r.as_ref(), Formula::Int(b) if *b <= 127)
            {
                found = true;
            }
        });
        found
    };
    assert!(
        !injects_127_on_n,
        "unguarded shift must NOT have any `n <= 127`-style fact injected; got {:?}",
        shift.formula
    );
}

/// The exact `signed_max` MIR: nested short-circuit `width>=1 && width<=127`
/// guard reaching `1i128 << (width-1)`. Mirrors the stage1 trustc MIR dump.
fn signed_max_fixture() -> VerifiableFunction {
    use trust_types::{AssertMessage, Projection};
    let func = VerifiableFunction {
        name: "signed_max".to_string(),
        def_path: "signed_max".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("width".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("_3".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("_4".into()) },
                LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
                LocalDecl { index: 6, ty: Ty::u32(), name: Some("_6".into()) },
                LocalDecl {
                    index: 7,
                    ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                    name: Some("_7".into()),
                },
                LocalDecl { index: 8, ty: Ty::Bool, name: Some("_8".into()) },
                LocalDecl {
                    index: 9,
                    ty: Ty::Tuple(vec![Ty::i128(), Ty::Bool]),
                    name: Some("_9".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(128, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        exhaustive_enum_unreachable: false,
                        discr: Operand::Move(Place::local(2)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(i128::MAX))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(9)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        exhaustive_enum_unreachable: false,
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(8))],
                        otherwise: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(127, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        exhaustive_enum_unreachable: false,
                        discr: Operand::Move(Place::local(4)),
                        targets: vec![(0, BlockId(8))],
                        otherwise: BlockId(4),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(7),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place {
                            local: 7,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(5),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Use(Operand::Move(Place {
                                local: 7,
                                projections: vec![Projection::Field(0)],
                            })),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(8),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(6)),
                                Operand::Constant(ConstValue::Uint(128, 32)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::local(8)),
                        expected: true,
                        msg: AssertMessage::Overflow(BinOp::Shl),
                        target: BlockId(6),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(6),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Constant(ConstValue::Int(1)),
                                Operand::Move(Place::local(6)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(9),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(5)),
                                Operand::Constant(ConstValue::Int(1)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place {
                            local: 9,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(7),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(7),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Move(Place {
                            local: 9,
                            projections: vec![Projection::Field(0)],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(9)),
                },
                BasicBlock {
                    id: BlockId(8),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(i128::MAX))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(9)),
                },
                BasicBlock { id: BlockId(9), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::i128(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    func
}

/// Build `many_paths`: `arms` switch arms from bb0 into bb1, `otherwise` to bb2.
/// With `arms > MAX_PATHS_PER_BLOCK` bb1 SATURATES, which is the state every
/// collapse test below needs to be in.
fn many_paths_fixture(arms: u128) -> VerifiableFunction {
    VerifiableFunction {
        name: "many_paths".to_string(),
        def_path: "many_paths".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: (0..arms).map(|value| (value, BlockId(1))).collect(),
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Saturation weakens a block to ONE UNGUARDED path, and the PATH MAP keeps
/// saying so — every consumer of `v2_build_path_guard_map` stays exactly as it
/// was. What the repair adds is a SEPARATE channel: the weakest condition that
/// is still a theorem about reaching the block, the disjunction of its in-edge
/// guards, which `generate_v2_safety_vcs` splices onto the rows that have no
/// violation condition of their own.
///
/// 65 switch arms into one block: over `MAX_PATHS_PER_BLOCK`, so the block DOES
/// saturate — that is what keeps this test on the path it guards.
#[test]
fn v2_path_guard_saturation_reports_the_in_edge_disjunction_separately() {
    let func = many_paths_fixture(65);

    let analysis = v2_analyze_path_guards(&func);
    assert_eq!(
        analysis.collapse,
        PathGuardCollapse::SaturatedBlocks,
        "the fixture's value is that 65 arms exceed MAX_PATHS_PER_BLOCK; if that \
         drifts the repair below is not being exercised"
    );
    let paths = analysis.paths.get(&BlockId(1)).expect("target block should be reachable");
    assert_eq!(paths.len(), 1);
    assert!(
        paths[0].is_empty(),
        "the PATH MAP itself is unchanged by the repair — a saturated block still \
         weakens to one unguarded path, so the map's other consumers are \
         unaffected: {paths:?}"
    );
    assert!(analysis.degraded.contains(&BlockId(1)), "bb1 is the degraded block");

    let Some(ReachSummary::Guards(edges)) = analysis.reachability.get(&BlockId(1)) else {
        panic!("bb1 must carry a real in-edge disjunction: {:?}", analysis.reachability);
    };
    assert_eq!(edges.len(), 65, "one guard per in-edge: {edges:?}");
    assert!(
        edges.iter().all(|(src, _)| *src == BlockId(0)),
        "each guard is sourced at the branch that created it: {edges:?}"
    );

    // FAIL-CLOSED CONTROL: give the block one UNGUARDED in-edge. The disjunction
    // is then `true` — which is POSITIVE information, not absence: the block is
    // reachable on every execution. Nothing is restored, and a content-free row
    // of that block must stay REFUTABLE.
    let mut with_goto = func.clone();
    with_goto.body.blocks.push(BasicBlock {
        id: BlockId(3),
        stmts: vec![],
        terminator: Terminator::Goto(BlockId(1)),
    });
    let analysis = v2_analyze_path_guards(&with_goto);
    assert_eq!(analysis.collapse, PathGuardCollapse::SaturatedBlocks);
    assert!(
        matches!(analysis.reachability.get(&BlockId(1)), Some(ReachSummary::Unconditional)),
        "an unguarded in-edge makes the disjunction `true`, which must be reported \
         as UNCONDITIONAL (reachable) and never as absence: {:?}",
        analysis.reachability
    );
}

/// THERE IS NO IN-DEGREE BUDGET, and this is the test that used to say there
/// was: an earlier `MAX_RESTORED_IN_EDGE_GUARDS` cap reported `Guards` up to a
/// fixed in-degree and `Unavailable` past it, and the collapse invariant
/// declines on `Unavailable`. Reporting ABSENCE because a real, available
/// condition is merely LARGE is not a safe answer — it is a bug lost.
///
/// The in-degree is a LINEAR quantity (at most the body's terminator-clause
/// count) and the restored disjunction is exactly one guard per in-edge, so the
/// row is linear in the in-degree — see the size rule on `ReachSummary::Guards`,
/// asserted in `path_guard_collapse_tests`. What changed is that no size is
/// treated as absence.
#[test]
fn v2_path_guard_in_edge_summary_has_no_size_budget() {
    for arms in [512usize, 513, 1024, 4096] {
        let analysis = v2_analyze_path_guards(&many_paths_fixture(arms as u128));
        assert_eq!(analysis.collapse, PathGuardCollapse::SaturatedBlocks, "{arms} arms");
        assert!(
            matches!(
                analysis.reachability.get(&BlockId(1)),
                Some(ReachSummary::Guards(e)) if e.len() == arms
            ),
            "{arms} in-edges must be summarised in full — there is no size at which a \
             real condition becomes ABSENCE: {:?}",
            analysis.reachability
        );
    }
}

fn formula_contains_or(formula: &Formula) -> bool {
    match formula {
        Formula::Or(_) => true,
        _ => formula.children().into_iter().any(formula_contains_or),
    }
}
