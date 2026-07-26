use trust_types::{
    AggregateKind, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
    VerifiableFunction,
};

use super::{
    FLOAT_ADD_TINY_OPERAND_BOUND, FLOAT_EXP_BOUND_FUEL, FLOAT_OVERFLOW_DISCHARGE_MARGIN,
    FloatNanMode, FloatRangeCtx, canonicalize_contract_index_segments, contract_range,
    derive_float_result_range, float_range, generate_callsite_precondition_vcs,
    generate_callsite_precondition_vcs_attributed, generate_v2_safety_vcs,
    parse_projection_suffix, precondition_interval_dominance, substitute_summary_params,
    v2_float_binop_cannot_overflow, v2_float_binop_cannot_overflow_at,
    v2_float_contract_magnitude_hypotheses, v2_float_overflow_witness_formula,
};
use crate::modular::{FunctionSummary, SummaryDatabase};
use std::sync::Arc;

fn f64s() -> Sort {
    Sort::Float { eb: 11, sb: 53 }
}
fn fp(v: f64) -> Formula {
    Formula::FpConst { bits: u128::from(v.to_bits()), eb: 11, sb: 53 }
}
/// `<name> <= <c>` / `<name> >= <c>` float bounds as the spec parser emits.
fn le_f(name: &str, c: f64) -> Formula {
    Formula::Le(Box::new(Formula::Var(name.into(), f64s())), Box::new(fp(c)))
}
fn ge_f(name: &str, c: f64) -> Formula {
    Formula::Ge(Box::new(Formula::Var(name.into(), f64s())), Box::new(fp(c)))
}
/// A symmetric two-sided bound `|name| <= c`, one `And` per contract clause.
fn both(name: &str, c: f64) -> Vec<Formula> {
    vec![Formula::And(vec![le_f(name, c), ge_f(name, -c)])]
}
fn fconst(v: f64) -> Operand {
    Operand::Constant(ConstValue::Float(v))
}
fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}
fn decl(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
    LocalDecl { index, ty, name: name.map(Into::into) }
}
fn make(
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
    return_ty: Ty,
    preconditions: Vec<Formula>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "fixture".into(),
        def_path: "test::fixture".into(),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count, return_ty },
        contracts: vec![],
        preconditions,
        postconditions: vec![],
        spec: Default::default(),
    }
}
fn range_forbid(
    func: &VerifiableFunction,
    block: Option<BlockId>,
    operand: &Operand,
) -> Option<(f64, f64)> {
    let ctx = FloatRangeCtx::new(func, None);
    float_range(
        &ctx,
        FloatNanMode::Forbid,
        block,
        operand,
        &mut Vec::new(),
        FLOAT_EXP_BOUND_FUEL,
    )
}
fn range_nob(
    func: &VerifiableFunction,
    block: Option<BlockId>,
    operand: &Operand,
) -> Option<(f64, f64)> {
    let ctx = FloatRangeCtx::new(func, None);
    float_range(
        &ctx,
        FloatNanMode::NanOrBounded,
        block,
        operand,
        &mut Vec::new(),
        FLOAT_EXP_BOUND_FUEL,
    )
}
fn float_overflow_kinds(func: &VerifiableFunction) -> Vec<VcKind> {
    generate_v2_safety_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { .. }))
        .map(|vc| vc.kind)
        .collect()
}

#[test]
fn margin_constants_are_the_documented_powers_of_two() {
    assert_eq!(FLOAT_OVERFLOW_DISCHARGE_MARGIN, 2f64.powi(1020));
    assert_eq!(FLOAT_ADD_TINY_OPERAND_BOUND, 2f64.powi(970));
}

// ---- F0: multi-def HULL (the recon-confirmed last-def-wins false proof) ----

/// `let mut t = <first>; if c { t = <second>; } t + t` — two whole-local
/// defs of `t` (_2) in blocks bb0/bb1, Add in the join bb2.
fn multi_def(first: f64, second: f64) -> VerifiableFunction {
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::Bool, Some("c")),
            decl(2, Ty::f64_ty(), Some("t")),
            decl(3, Ty::f64_ty(), None),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(Place::local(2), Rvalue::Use(fconst(first)))],
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
                stmts: vec![assign(Place::local(2), Rvalue::Use(fconst(second)))],
                terminator: Terminator::Goto(BlockId(2)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![
                    assign(
                        Place::local(3),
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(2)),
                        ),
                    ),
                    assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(3)))),
                ],
                terminator: Terminator::Return,
            },
        ],
        1,
        Ty::f64_ty(),
        vec![],
    )
}

#[test]
fn multi_def_big_then_small_add_is_not_discharged() {
    // REGRESSION (recon R1.Q3 / F0): the old scan took the LAST def in scan
    // order (the 1.0 in bb1), discharging `t + t` while the c=false path
    // computes 1e308 + 1e308 = +inf — a reachable FALSE PROOF. The hull
    // [1.0, 1e308] makes the Add interval overflow → obligation KEPT.
    let func = multi_def(1e308, 1.0);
    let t = Operand::Copy(Place::local(2));
    assert!(!v2_float_binop_cannot_overflow(&func, BinOp::Add, &t, &t));
    assert!(
        float_overflow_kinds(&func)
            .iter()
            .any(|k| matches!(k, VcKind::FloatOverflowToInfinity { op: BinOp::Add, .. })),
        "the multi-def Add must mint its obligation"
    );
}

#[test]
fn multi_def_hull_of_small_consts_discharges() {
    let func = multi_def(1.0, 2.0);
    let t = Operand::Copy(Place::local(2));
    let (lo, hi) = range_forbid(&func, None, &t).expect("hull of {1.0, 2.0}");
    assert!(
        lo <= 1.0 && hi >= 2.0 && lo >= 0.5 && hi <= 4.0,
        "hull ≈ [1, 2], got [{lo}, {hi}]"
    );
    assert!(v2_float_binop_cannot_overflow(&func, BinOp::Add, &t, &t));
    assert!(float_overflow_kinds(&func).is_empty(), "small hull must discharge the Add");
}

#[test]
fn reassigned_param_read_fails_closed() {
    // SOUNDNESS (self-review catch): `fn f(mut x: f64) { let a = x;
    // x = 1.0; a + a }` — the param's ENTRY value is a statement-invisible
    // def, so the visible-def hull [1.0, 1.0] does NOT enclose `a` (the
    // unbounded entry `x`). Both the whole-local read of `x` and the
    // copy `a` must refuse.
    let func = make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("x")),
            decl(2, Ty::f64_ty(), Some("a")),
            decl(3, Ty::f64_ty(), None),
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(Place::local(1), Rvalue::Use(fconst(1.0))),
                assign(
                    Place::local(3),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(2)),
                        Operand::Copy(Place::local(2)),
                    ),
                ),
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(3)))),
            ],
            terminator: Terminator::Return,
        }],
        1,
        Ty::f64_ty(),
        vec![],
    );
    assert_eq!(range_forbid(&func, None, &Operand::Copy(Place::local(1))), None);
    assert_eq!(range_nob(&func, None, &Operand::Copy(Place::local(2))), None);
    let a = Operand::Copy(Place::local(2));
    assert!(!v2_float_binop_cannot_overflow(&func, BinOp::Add, &a, &a));
    assert!(!float_overflow_kinds(&func).is_empty());
}

#[test]
fn reassigned_param_aggregate_is_not_field_traced() {
    // SOUNDNESS twin of the above for F3: `t = (1.0, 2.0)` on a PARAM `t`
    // is not a unique construction — a read of `t.0` before the write sees
    // the caller's aggregate. No interval may be claimed.
    let tuple_ty = Ty::Tuple(vec![Ty::f64_ty(), Ty::f64_ty()]);
    let func = make(
        vec![decl(0, Ty::f64_ty(), None), decl(1, tuple_ty, Some("t"))],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::field(1, 0)))),
                assign(
                    Place::local(1),
                    Rvalue::Aggregate(AggregateKind::Tuple, vec![fconst(1.0), fconst(2.0)]),
                ),
            ],
            terminator: Terminator::Return,
        }],
        1,
        Ty::f64_ty(),
        vec![],
    );
    assert_eq!(range_nob(&func, None, &Operand::Copy(Place::field(1, 0))), None);
    assert_eq!(range_forbid(&func, None, &Operand::Copy(Place::field(1, 0))), None);
}

#[test]
fn opaque_terminator_poisons_def_tracing() {
    // SOUNDNESS: an `Opaque` terminator (inline asm) may write ANY local
    // invisibly — no def set may be trusted anywhere in the function.
    let func = make(
        vec![decl(0, Ty::f64_ty(), None), decl(1, Ty::f64_ty(), Some("t"))],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(Place::local(1), Rvalue::Use(fconst(1.0)))],
                terminator: Terminator::Opaque {
                    kind: "asm".into(),
                    targets: vec![BlockId(1)],
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::Use(Operand::Copy(Place::local(1))),
                )],
                terminator: Terminator::Return,
            },
        ],
        0,
        Ty::f64_ty(),
        vec![],
    );
    assert_eq!(range_nob(&func, None, &Operand::Copy(Place::local(1))), None);
}

#[test]
fn self_referential_def_fails_closed() {
    // `t = 1.0; loop { t = t + 1.0 }` — the accumulator def reads its own
    // local; the visiting cycle guard must refuse a closed form.
    let func = make(
        vec![decl(0, Ty::f64_ty(), None), decl(1, Ty::f64_ty(), Some("t"))],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(Place::local(1), Rvalue::Use(fconst(1.0)))],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(
                    Place::local(1),
                    Rvalue::BinaryOp(BinOp::Add, Operand::Copy(Place::local(1)), fconst(1.0)),
                )],
                terminator: Terminator::Goto(BlockId(1)),
            },
        ],
        0,
        Ty::f64_ty(),
        vec![],
    );
    let t = Operand::Copy(Place::local(1));
    assert_eq!(range_forbid(&func, None, &t), None);
    assert_eq!(range_nob(&func, None, &t), None);
    assert!(!v2_float_binop_cannot_overflow(&func, BinOp::Mul, &t, &t));
}

// ---- F3: unique-aggregate element tracing ----

/// `_2 = (self.0, self.1); _3 = _2.0 * _2.1` with optional two-sided field
/// contract and optional post-construction element store.
fn tuple_aggregate(contracted: bool, projected_store: bool) -> VerifiableFunction {
    let mut stmts = vec![
        assign(
            Place::local(2),
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![Operand::Copy(Place::field(1, 0)), Operand::Copy(Place::field(1, 1))],
            ),
        ),
        assign(
            Place::local(3),
            Rvalue::BinaryOp(
                BinOp::Mul,
                Operand::Copy(Place::field(2, 0)),
                Operand::Copy(Place::field(2, 1)),
            ),
        ),
        assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(3)))),
    ];
    if projected_store {
        // SOUNDNESS twin: an element overwrite after construction breaks
        // the frozen-element argument — tracing must refuse.
        stmts.insert(1, assign(Place::field(2, 0), Rvalue::Use(fconst(1e308))));
    }
    let tuple_ty = Ty::Tuple(vec![Ty::f64_ty(), Ty::f64_ty()]);
    let pre = if contracted {
        vec![Formula::And(vec![
            le_f("self.0", 1e30),
            ge_f("self.0", -1e30),
            le_f("self.1", 1e30),
            ge_f("self.1", -1e30),
        ])]
    } else {
        vec![]
    };
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, tuple_ty.clone(), Some("self")),
            decl(2, tuple_ty, None),
            decl(3, Ty::f64_ty(), None),
        ],
        vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
        1,
        Ty::f64_ty(),
        pre,
    )
}

#[test]
fn tuple_aggregate_element_traces_to_contract() {
    let func = tuple_aggregate(true, false);
    let e0 = Operand::Copy(Place::field(2, 0));
    let e1 = Operand::Copy(Place::field(2, 1));
    assert_eq!(range_forbid(&func, None, &e0), Some((-1e30, 1e30)));
    assert!(v2_float_binop_cannot_overflow(&func, BinOp::Mul, &e0, &e1));
    assert!(float_overflow_kinds(&func).is_empty());
}

#[test]
fn tuple_aggregate_uncontracted_element_fails_closed() {
    let func = tuple_aggregate(false, false);
    let e0 = Operand::Copy(Place::field(2, 0));
    assert_eq!(range_forbid(&func, None, &e0), None);
    assert!(!float_overflow_kinds(&func).is_empty(), "unbounded elements keep the Mul VC");
}

#[test]
fn aggregate_with_projected_element_store_fails_closed() {
    // `_2.0 = 1e308` after construction: the contracted element bound must
    // NOT be applied to the overwritten slot.
    let func = tuple_aggregate(true, true);
    let e0 = Operand::Copy(Place::field(2, 0));
    assert_eq!(range_forbid(&func, None, &e0), None);
    assert!(!float_overflow_kinds(&func).is_empty());
}

// ---- F2 + Div: dominating float guards ----

/// `if <guard_lhs> > 1e-20 { a / len } else { 0.0 }`, with a two-sided
/// contract on the numerator `a` only. `both_edges` routes BOTH switch
/// edges into the div block (non-dominating guard); `false_edge` puts the
/// division on the guard's FALSE edge (fact = `¬(len > c)`, NaN-inclusive);
/// `via_copy_temp` compares a copy temp `_5 = copy len` instead of `len`.
fn guarded_div(
    guard_lhs: usize,
    both_edges: bool,
    false_edge: bool,
    via_copy_temp: bool,
) -> VerifiableFunction {
    let mut bb0_stmts = Vec::new();
    let compared = if via_copy_temp {
        bb0_stmts
            .push(assign(Place::local(5), Rvalue::Use(Operand::Copy(Place::local(guard_lhs)))));
        5
    } else {
        guard_lhs
    };
    bb0_stmts.push(assign(
        Place::local(3),
        Rvalue::BinaryOp(BinOp::Gt, Operand::Copy(Place::local(compared)), fconst(1e-20)),
    ));
    let (targets, otherwise) = if both_edges {
        (vec![(0u128, BlockId(1))], BlockId(1))
    } else if false_edge {
        (vec![(0u128, BlockId(1))], BlockId(2))
    } else {
        (vec![(0u128, BlockId(2))], BlockId(1))
    };
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("a")),
            decl(2, Ty::f64_ty(), Some("len")),
            decl(3, Ty::Bool, None),
            decl(4, Ty::f64_ty(), None),
            decl(5, Ty::f64_ty(), None),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: bb0_stmts,
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(3)),
                    targets,
                    otherwise,
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    assign(
                        Place::local(4),
                        Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    ),
                    assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(4)))),
                ],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(Place::local(0), Rvalue::Use(fconst(0.0)))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
        Ty::f64_ty(),
        both("a", 1e30),
    )
}

fn div_discharges(func: &VerifiableFunction) -> bool {
    v2_float_binop_cannot_overflow_at(
        func,
        Some(BlockId(1)),
        None,
        BinOp::Div,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
    )
}

#[test]
fn guarded_divisor_discharges_div_overflow() {
    // `len > 1e-20` dominates the div: |a/len| <= 1e30 / 1e-20 = 1e50, far
    // below the 2^1020 margin — the obligation is provably unfireable.
    let func = guarded_div(2, false, false, false);
    assert!(div_discharges(&func));
    assert!(float_overflow_kinds(&func).is_empty(), "guarded div must mint no VC");
}

#[test]
fn guarded_divisor_through_copy_temp_discharges() {
    // Real MIR often compares a copy temp (`_5 = copy len; if _5 > c`);
    // the single-def alias hop must connect the fact to the divisor.
    let func = guarded_div(2, false, false, true);
    assert!(div_discharges(&func));
}

#[test]
fn guard_on_wrong_local_keeps_div_obligation() {
    // The guard tests `a`, not the divisor — no magnitude floor for `len`.
    let func = guarded_div(1, false, false, false);
    assert!(!div_discharges(&func));
    assert!(
        float_overflow_kinds(&func)
            .iter()
            .any(|k| matches!(k, VcKind::FloatOverflowToInfinity { op: BinOp::Div, .. })),
    );
}

#[test]
fn non_dominating_guard_keeps_div_obligation() {
    // BOTH switch edges reach the div block: the fact is not on every
    // path, the intersection is empty, the obligation stays.
    let func = guarded_div(2, true, false, false);
    assert!(!div_discharges(&func));
}

#[test]
fn false_edge_guard_gives_no_bound() {
    // SOUNDNESS (NaN channel): on the FALSE edge the fact is `¬(len >
    // 1e-20)` — satisfied by `len = NaN` and by every tiny/zero divisor,
    // so inverting it into `len <= 1e-20` (or ANY bound) would be a
    // false-proof channel. The div there genuinely can overflow: keep it.
    let func = guarded_div(2, false, true, false);
    assert!(!div_discharges(&func));
    assert!(!float_overflow_kinds(&func).is_empty());
}

#[test]
fn zero_straddling_divisor_keeps_div_obligation() {
    // Contract |len| <= 1.0 straddles zero: no sign-definite floor.
    let mut func = guarded_div(1, true, false, false); // guard is inert here
    func.preconditions = vec![Formula::And(vec![
        le_f("a", 1e30),
        ge_f("a", -1e30),
        le_f("len", 1.0),
        ge_f("len", -1.0),
    ])];
    assert!(!div_discharges(&func));
}

#[test]
fn contract_sign_definite_divisor_discharges_div() {
    // `len ∈ [1e-3, 1e3]` (strictly positive): m = 1e-3, |a/len| <= 1e33.
    let mut func = guarded_div(1, true, false, false);
    func.preconditions = vec![Formula::And(vec![
        le_f("a", 1e30),
        ge_f("a", -1e30),
        le_f("len", 1e3),
        ge_f("len", 1e-3),
    ])];
    assert!(v2_float_binop_cannot_overflow(
        &func,
        BinOp::Div,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
    ));
}

#[test]
fn unguarded_float_div_emits_float_overflow_vc() {
    // Baseline emission (F1/§4): an unbounded float division now mints a
    // FloatOverflowToInfinity{Div} witness obligation.
    let mut func = guarded_div(1, true, false, false);
    func.preconditions = vec![];
    let kinds = float_overflow_kinds(&func);
    assert!(
        kinds
            .iter()
            .any(|k| matches!(k, VcKind::FloatOverflowToInfinity { op: BinOp::Div, .. })),
        "got {kinds:?}"
    );
}

// ---- Sub emission (§4) ----

fn sub_func(bounded: bool) -> VerifiableFunction {
    let pre = if bounded {
        vec![Formula::And(vec![
            le_f("a", 1e30),
            ge_f("a", -1e30),
            le_f("b", 1e30),
            ge_f("b", -1e30),
        ])]
    } else {
        vec![]
    };
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("a")),
            decl(2, Ty::f64_ty(), Some("b")),
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(0),
                Rvalue::BinaryOp(
                    BinOp::Sub,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
            )],
            terminator: Terminator::Return,
        }],
        2,
        Ty::f64_ty(),
        pre,
    )
}

#[test]
fn unbounded_float_sub_emits_overflow_vc() {
    let kinds = float_overflow_kinds(&sub_func(false));
    assert_eq!(kinds.len(), 1, "got {kinds:?}");
    assert!(matches!(
        &kinds[0],
        VcKind::FloatOverflowToInfinity { op: BinOp::Sub, operand_ty: Ty::Float { width: 64 } }
    ));
}

#[test]
fn bounded_float_sub_discharges() {
    assert!(float_overflow_kinds(&sub_func(true)).is_empty());
}

// ---- tiny-addend one-sided Add/Sub discharge ----

#[test]
fn tiny_literal_addend_discharges_with_unbounded_other_operand() {
    // |0.05| < 2^970 = ulp(MAX)/2: a finite `x` cannot be pushed past the
    // round-to-inf boundary, whatever its value (a non-finite `x`
    // propagates, which is not an overflow OF this op).
    let func = sub_func(false);
    let x = Operand::Copy(Place::local(1));
    for op in [BinOp::Add, BinOp::Sub] {
        assert!(v2_float_binop_cannot_overflow(&func, op, &x, &fconst(0.05)), "{op:?}");
        assert!(v2_float_binop_cannot_overflow(&func, op, &fconst(0.05), &x), "{op:?}");
    }
}

#[test]
fn large_literal_addend_does_not_discharge_unbounded_add() {
    // SOUNDNESS twin (round-10 shape): 1e300 (2^996 ≥ 2^970) + a
    // near-MAX unbounded operand DOES overflow — no one-sided discharge.
    let func = sub_func(false);
    let x = Operand::Copy(Place::local(1));
    for op in [BinOp::Add, BinOp::Sub] {
        assert!(!v2_float_binop_cannot_overflow(&func, op, &x, &fconst(1e300)), "{op:?}");
    }
}

// ---- interval rounding edges ----

#[test]
fn near_max_bounds_keep_add_and_mul_obligations() {
    // Contract bounds at ±f64::MAX: the Add endpoint (2·MAX) and the Mul
    // endpoint (MAX²) are non-finite → fail-closed, obligations kept.
    let mut func = sub_func(true);
    func.preconditions = vec![Formula::And(vec![
        le_f("a", f64::MAX),
        ge_f("a", -f64::MAX),
        le_f("b", f64::MAX),
        ge_f("b", -f64::MAX),
    ])];
    let (a, b) = (Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2)));
    for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
        assert!(!v2_float_binop_cannot_overflow(&func, op, &a, &b), "{op:?}");
    }
}

#[test]
fn margin_boundary_is_respected_outward() {
    // Bounds exactly AT the 2^1020 margin: the Add interval reaches
    // ±2^1021 (and the outward bump pushes past even an exact hit) — kept.
    // At 1e300 the Add (2e300 ≪ 2^1020) discharges while the Mul (1e600 →
    // inf) stays: the margin separates the two on the same fixture.
    let mut func = sub_func(true);
    let (a, b) = (Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2)));
    func.preconditions = vec![Formula::And(vec![
        le_f("a", FLOAT_OVERFLOW_DISCHARGE_MARGIN),
        ge_f("a", -FLOAT_OVERFLOW_DISCHARGE_MARGIN),
        le_f("b", FLOAT_OVERFLOW_DISCHARGE_MARGIN),
        ge_f("b", -FLOAT_OVERFLOW_DISCHARGE_MARGIN),
    ])];
    assert!(!v2_float_binop_cannot_overflow(&func, BinOp::Add, &a, &b));
    func.preconditions = vec![Formula::And(vec![
        le_f("a", 1e300),
        ge_f("a", -1e300),
        le_f("b", 1e300),
        ge_f("b", -1e300),
    ])];
    assert!(v2_float_binop_cannot_overflow(&func, BinOp::Add, &a, &b));
    assert!(!v2_float_binop_cannot_overflow(&func, BinOp::Mul, &a, &b));
}

// ---- F4: index canonicalization + uniform-index hull ----

#[test]
fn canonicalize_index_segments_unit() {
    let canon = canonicalize_contract_index_segments;
    assert_eq!(canon("self.0[3;min=4].1"), "self.0[3].1");
    assert_eq!(canon("arr[0;min=2]"), "arr[0]");
    assert_eq!(canon("x[_5]"), "x[_5]"); // runtime index: untouched
    assert_eq!(canon("x[-1;min=4]"), "x[-1;min=4]"); // from-end: untouched
    assert_eq!(canon("x[0;slice]"), "x[0;slice]"); // slice: untouched
    assert_eq!(canon("x[2..4]"), "x[2..4]"); // subslice: untouched
    assert_eq!(canon("plain.0"), "plain.0");
}

/// `arr: [f64; 2]` (param 1), `i: usize` (param 2), read `arr[i]`.
fn array_param_func(pre: Vec<Formula>) -> VerifiableFunction {
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::Array { elem: Box::new(Ty::f64_ty()), len: 2 }, Some("arr")),
            decl(2, Ty::Int { width: 64, signed: false }, Some("i")),
        ],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
        2,
        Ty::f64_ty(),
        pre,
    )
}

#[test]
fn uniform_index_hull_over_all_elements() {
    // Both elements two-sided → runtime read gets the hull.
    let mut pre = both("arr[0]", 1e10);
    pre.extend(both("arr[1]", 1e20));
    let func = array_param_func(pre);
    let read = Place { local: 1, projections: vec![Projection::Index(2)] };
    assert_eq!(contract_range(&func, &read), Some((-1e20, 1e20)));
}

#[test]
fn uniform_index_with_missing_element_fails_closed() {
    // SOUNDNESS twin: arr[1] has no lower bound — the runtime read could
    // land there, so NO interval may be claimed.
    let mut pre = both("arr[0]", 1e10);
    pre.push(Formula::And(vec![le_f("arr[1]", 1e20)]));
    let func = array_param_func(pre);
    let read = Place { local: 1, projections: vec![Projection::Index(2)] };
    assert_eq!(contract_range(&func, &read), None);
}

#[test]
fn constant_index_render_matches_contract_spelling() {
    // A `ConstantIndex` read renders `[0;min=2]`; canonicalization maps it
    // onto the parser-side `arr[0]` bound.
    let func = array_param_func(both("arr[0]", 1e10));
    let read = Place {
        local: 1,
        projections: vec![Projection::ConstantIndex {
            offset: 0,
            min_length: 2,
            from_end: false,
        }],
    };
    assert_eq!(contract_range(&func, &read), Some((-1e10, 1e10)));
}

// ---- σ suffix parsing / bracket rebinding ----

#[test]
fn parse_projection_suffix_unit() {
    assert_eq!(parse_projection_suffix(".0"), Some(vec![Projection::Field(0)]));
    assert_eq!(
        parse_projection_suffix("[3]"),
        Some(vec![Projection::ConstantIndex { offset: 3, min_length: 4, from_end: false }])
    );
    assert_eq!(
        parse_projection_suffix("*.2"),
        Some(vec![Projection::Deref, Projection::Field(2)])
    );
    assert_eq!(
        parse_projection_suffix(".0[3].1"),
        Some(vec![
            Projection::Field(0),
            Projection::ConstantIndex { offset: 3, min_length: 4, from_end: false },
            Projection::Field(1),
        ])
    );
    // Adversarial: callee-namespace-relative / malformed tokens refuse.
    assert_eq!(parse_projection_suffix("[_5]"), None);
    assert_eq!(parse_projection_suffix("@1"), None);
    assert_eq!(parse_projection_suffix(""), None);
    assert_eq!(parse_projection_suffix("[3"), None);
    assert_eq!(parse_projection_suffix(".x"), None);
}

#[test]
fn bracket_suffix_rebinds_to_actual() {
    // F4 σ half: `self.0[3].1` under `self -> a` becomes `a.0[3].1`.
    let precond =
        Formula::Le(Box::new(Formula::Var("self.0[3].1".into(), f64s())), Box::new(fp(1e30)));
    let replacements = vec![("self".to_string(), Formula::Var("a".into(), Sort::Int))];
    let out = substitute_summary_params(&precond, &replacements);
    assert_eq!(
        out,
        Formula::Le(Box::new(Formula::Var("a.0[3].1".into(), f64s())), Box::new(fp(1e30)))
    );
}

#[test]
fn runtime_index_suffix_falls_to_fresh_sigma_var() {
    // SOUNDNESS twin: `self[_5]` names a CALLEE local — reattaching it to
    // the caller would silently reference an unrelated caller local.
    let precond =
        Formula::Le(Box::new(Formula::Var("self[_5]".into(), f64s())), Box::new(fp(1e30)));
    let replacements = vec![("self".to_string(), Formula::Var("a".into(), Sort::Int))];
    let out = substitute_summary_params(&precond, &replacements);
    let Formula::Le(lhs, _) = &out else { panic!("expected Le, got {out:?}") };
    let name = lhs.var_name().expect("lhs is a var");
    assert!(name.starts_with("__trust_sigma_field__"), "got {name}");
}

// ---- F5: structural precondition-interval dominance ----

/// Caller with `|a.0| <= 1e30` calling `callee(a)`; the callee requires
/// `|self.0| <= bound`.
fn f5_caller() -> VerifiableFunction {
    make(
        vec![
            decl(0, Ty::Unit, None),
            decl(1, Ty::Tuple(vec![Ty::f64_ty()]), Some("a")),
            decl(2, Ty::f64_ty(), None),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "callee".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(2),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
        Ty::Unit,
        both("a.0", 1e30),
    )
}

fn f5_db(precondition: Formula) -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    db.insert(
        FunctionSummary::new("callee")
            .with_param_names(vec!["self".into()])
            .with_precondition(precondition),
    );
    db
}

fn callee_bound_pre(bound: f64) -> Formula {
    Formula::And(vec![le_f("self.0", bound), ge_f("self.0", -bound)])
}

#[test]
fn f5_equal_and_wider_requirements_skip_the_obligation() {
    let func = f5_caller();
    for bound in [1e30, 1e40] {
        let db = f5_db(callee_bound_pre(bound));
        let vcs = generate_callsite_precondition_vcs(&func, &db);
        assert!(vcs.is_empty(), "bound {bound}: {vcs:?}");
        assert!(generate_callsite_precondition_vcs_attributed(&func, &db).is_empty());
    }
}

#[test]
fn f5_narrower_requirement_emits_the_obligation() {
    // The caller only knows |a.0| <= 1e30; the callee wants <= 1e20 — the
    // interval does NOT dominate, so the VC must be minted as before.
    let func = f5_caller();
    let db = f5_db(callee_bound_pre(1e20));
    let vcs = generate_callsite_precondition_vcs(&func, &db);
    assert_eq!(vcs.len(), 1, "{vcs:?}");
    assert!(matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee == "callee"));
    assert_eq!(generate_callsite_precondition_vcs_attributed(&func, &db).len(), 1);
}

#[test]
fn f5_one_sided_requirement_is_not_skipped() {
    // Both sides are required per var (the audited magnitude-bound shape);
    // a one-sided callee requirement keeps its obligation even though the
    // upper conjunct alone would check out.
    let func = f5_caller();
    let db = f5_db(Formula::And(vec![le_f("self.0", 1e30)]));
    assert_eq!(generate_callsite_precondition_vcs(&func, &db).len(), 1);
}

#[test]
fn f5_int_shaped_requirement_is_not_skipped() {
    // A non-float conjunct disqualifies the WHOLE precondition from the
    // structural skip (fail-closed to ordinary emission).
    let func = f5_caller();
    let db = f5_db(Formula::Le(
        Box::new(Formula::Var("self.0".into(), Sort::Int)),
        Box::new(Formula::Int(5)),
    ));
    assert_eq!(generate_callsite_precondition_vcs(&func, &db).len(), 1);
}

#[test]
fn f5_strict_requirement_needs_strictly_interior_endpoints() {
    // `self.0 < 1e30` is NOT satisfied by an interval whose hi IS 1e30…
    let func = f5_caller();
    let strict = Formula::And(vec![
        Formula::Lt(Box::new(Formula::Var("self.0".into(), f64s())), Box::new(fp(1e30))),
        Formula::Gt(Box::new(Formula::Var("self.0".into(), f64s())), Box::new(fp(-1e30))),
    ]);
    assert_eq!(generate_callsite_precondition_vcs(&func, &f5_db(strict)).len(), 1);
    // …while a strictly wider strict requirement is.
    let strict_wider = Formula::And(vec![
        Formula::Lt(Box::new(Formula::Var("self.0".into(), f64s())), Box::new(fp(1e31))),
        Formula::Gt(Box::new(Formula::Var("self.0".into(), f64s())), Box::new(fp(-1e31))),
    ]);
    assert!(generate_callsite_precondition_vcs(&func, &f5_db(strict_wider)).is_empty());
}

// ---- strict-mode NaN discipline (clamp channel) ----

/// `r = x.clamp(0.0, 1.0)` with `x` UNBOUNDED (possibly NaN).
fn clamp_func() -> VerifiableFunction {
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("x")),
            decl(2, Ty::f64_ty(), Some("r")),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "core::f64::<impl f64>::clamp".to_string(),
                    args: vec![Operand::Copy(Place::local(1)), fconst(0.0), fconst(1.0)],
                    dest: Place::local(2),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::Use(Operand::Copy(Place::local(2))),
                )],
                terminator: Terminator::Return,
            },
        ],
        1,
        Ty::f64_ty(),
        vec![],
    )
}

#[test]
fn clamp_of_unbounded_self_is_nan_tolerant_only() {
    // `clamp` passes a NaN self THROUGH: the NaN-tolerant mode may bound
    // the non-NaN outcomes (overflow discharge stays truthful — NaN is not
    // ±inf), but the STRICT mode must refuse (F5/F6 evaluate comparisons,
    // which a NaN falsifies).
    let func = clamp_func();
    let r = Operand::Copy(Place::local(2));
    assert_eq!(range_nob(&func, Some(BlockId(1)), &r), Some((0.0, 1.0)));
    assert_eq!(range_forbid(&func, Some(BlockId(1)), &r), None);
}

#[test]
fn f5_dominance_rejects_possibly_nan_actual() {
    // callee requires v ∈ [0, 1]; the actual is clamp(x, 0, 1) with x
    // unbounded — NaN reaches the callee with the requirement FALSE, so
    // the structural skip must refuse (fail-closed to emission).
    let func = clamp_func();
    let ctx = FloatRangeCtx::new(&func, None);
    let pre = Formula::And(vec![le_f("v", 1.0), ge_f("v", 0.0)]);
    assert!(!precondition_interval_dominance(
        &ctx,
        BlockId(1),
        &pre,
        &["v".to_string()],
        &[Operand::Copy(Place::local(2))],
        &mut Vec::new(),
        FLOAT_EXP_BOUND_FUEL,
    ));
    // Positive control: a literal actual inside the interval dominates.
    assert!(precondition_interval_dominance(
        &ctx,
        BlockId(1),
        &pre,
        &["v".to_string()],
        &[fconst(0.5)],
        &mut Vec::new(),
        FLOAT_EXP_BOUND_FUEL,
    ));
}

// ---- F6: interprocedural result ranges ----

/// `r = leaf(x); r * r` — the Mul is dischargeable only through leaf's
/// summary interval.
fn summary_caller(pre: Vec<Formula>) -> VerifiableFunction {
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("x")),
            decl(2, Ty::f64_ty(), Some("r")),
            decl(3, Ty::f64_ty(), None),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "leaf".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(2),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    assign(
                        Place::local(3),
                        Rvalue::BinaryOp(
                            BinOp::Mul,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(2)),
                        ),
                    ),
                    assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(3)))),
                ],
                terminator: Terminator::Goto(BlockId(2)),
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
        Ty::f64_ty(),
        pre,
    )
}

fn mul_discharges_with(func: &VerifiableFunction, db: &SummaryDatabase) -> bool {
    v2_float_binop_cannot_overflow_at(
        func,
        Some(BlockId(1)),
        Some(db),
        BinOp::Mul,
        &Operand::Copy(Place::local(2)),
        &Operand::Copy(Place::local(2)),
    )
}

#[test]
fn summary_result_range_discharges_when_preconditions_empty() {
    let func = summary_caller(vec![]);
    let mut db = SummaryDatabase::new();
    db.insert(FunctionSummary::new("leaf").with_result_range(-2.0, 2.0));
    assert!(mul_discharges_with(&func, &db));
}

#[test]
fn absent_or_forged_summary_range_is_not_consumed() {
    let func = summary_caller(vec![]);
    // No result_range at all (the production contract-summary shape).
    let mut db = SummaryDatabase::new();
    db.insert(FunctionSummary::new("leaf"));
    assert!(!mul_discharges_with(&func, &db));
    // Forged/malformed intervals are re-validated and refused.
    for (lo, hi) in [(f64::NAN, 2.0), (3.0, 2.0), (f64::NEG_INFINITY, 0.0)] {
        let mut db = SummaryDatabase::new();
        db.insert(FunctionSummary::new("leaf").with_result_range(lo, hi));
        assert!(!mul_discharges_with(&func, &db), "({lo}, {hi}) must be refused");
    }
}

#[test]
fn summary_range_gated_on_precondition_dominance_at_the_site() {
    // leaf requires |v| <= 1e30 (bare formal). With the caller contract
    // |x| <= 1e30 the site re-establishes it structurally → the interval
    // is consumable; without the contract it is NOT (assume-guarantee, no
    // reliance on the separately-emitted Precondition VC).
    let summary = || {
        FunctionSummary::new("leaf")
            .with_param_names(vec!["v".into()])
            .with_precondition(Formula::And(vec![le_f("v", 1e30), ge_f("v", -1e30)]))
            .with_result_range(-4.0, 4.0)
    };
    let mut db = SummaryDatabase::new();
    db.insert(summary());
    let with_contract = summary_caller(both("x", 1e30));
    assert!(mul_discharges_with(&with_contract, &db));
    let without_contract = summary_caller(vec![]);
    assert!(!mul_discharges_with(&without_contract, &db));
}

// ---- F6 derivation ----

#[test]
fn derive_result_range_hulls_the_return_defs() {
    // `if c { 1.0 } else { 2.5 }` — hull of the two `_0` defs.
    let func = make(
        vec![decl(0, Ty::f64_ty(), None), decl(1, Ty::Bool, Some("c"))],
        vec![
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
                stmts: vec![assign(Place::local(0), Rvalue::Use(fconst(1.0)))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(Place::local(0), Rvalue::Use(fconst(2.5)))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
        Ty::f64_ty(),
        vec![],
    );
    assert_eq!(derive_float_result_range(&func), Some((1.0, 2.5)));
}

#[test]
fn derive_result_range_rejects_non_f64_returns() {
    let func = make(
        vec![decl(0, Ty::Unit, None)],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
        0,
        Ty::Unit,
        vec![],
    );
    assert_eq!(derive_float_result_range(&func), None);
}

#[test]
fn derive_result_range_uses_per_def_guard_context() {
    // The div def sits under its own dominating `len ∈ [1e-3, 1e3]`-style
    // contract; the hull over {a/len, 0.0} must come out bounded (each _0
    // def is traced at ITS OWN block).
    let mut func = guarded_div(1, true, false, false);
    func.preconditions = vec![Formula::And(vec![
        le_f("a", 1e30),
        ge_f("a", -1e30),
        le_f("len", 1e3),
        ge_f("len", 1e-3),
    ])];
    let (lo, hi) = derive_float_result_range(&func).expect("bounded hull");
    assert!(lo <= 0.0 && hi >= 0.0, "the else-branch 0.0 is inside, got [{lo}, {hi}]");
    assert!(hi <= 1.001e33 && lo >= -1.001e33, "quotient bound ~1e33, got [{lo}, {hi}]");
}

/// `let m = len.abs(); if m > 1e-20 { a / len }` — the idiomatic abs-form
/// divisor guard. `reseat` adds a second whole-local def of `len` AFTER the
/// abs call, which must defeat the indirected floor (the guarded magnitude
/// is no longer the divided value).
fn abs_guarded_div(reseat: bool) -> VerifiableFunction {
    let mut bb1_stmts = vec![assign(
        Place::local(3),
        Rvalue::BinaryOp(BinOp::Gt, Operand::Copy(Place::local(5)), fconst(1e-20)),
    )];
    if reseat {
        bb1_stmts.insert(0, assign(Place::local(2), Rvalue::Use(fconst(2.0))));
    }
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("a")),
            decl(2, Ty::f64_ty(), Some("len")),
            decl(3, Ty::Bool, None),
            decl(4, Ty::f64_ty(), None),
            decl(5, Ty::f64_ty(), None),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "core::f64::<impl f64>::abs".to_string(),
                    args: vec![Operand::Copy(Place::local(2))],
                    dest: Place::local(5),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: bb1_stmts,
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(3)),
                    targets: vec![(0u128, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![
                    assign(
                        Place::local(4),
                        Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    ),
                    assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(4)))),
                ],
                terminator: Terminator::Goto(BlockId(4)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![assign(Place::local(0), Rvalue::Use(fconst(0.0)))],
                terminator: Terminator::Goto(BlockId(4)),
            },
            BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
        Ty::f64_ty(),
        both("a", 1e30),
    )
}

#[test]
fn abs_guarded_divisor_discharges_div_overflow() {
    // `|a| <= 1e30`, `|len| > 1e-20` via the abs temp: |a/len| <= 1e50 —
    // provably unfireable through the abs indirection.
    let func = abs_guarded_div(false);
    assert!(v2_float_binop_cannot_overflow_at(
        &func,
        Some(BlockId(2)),
        None,
        BinOp::Div,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
    ));
    assert!(float_overflow_kinds(&func).is_empty(), "abs-guarded div must mint no VC");
}

#[test]
fn abs_guard_on_reseated_divisor_keeps_div_obligation() {
    // SOUNDNESS twin: `len` is reseated to 2.0 AFTER the abs call — the
    // guarded magnitude is the OLD value, so the floor must decline and
    // the obligation stay.
    let func = abs_guarded_div(true);
    assert!(!v2_float_binop_cannot_overflow_at(
        &func,
        Some(BlockId(2)),
        None,
        BinOp::Div,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
    ));
}

#[test]
fn guard_floor_quotient_feeds_downstream_product() {
    // The normalized()->scale() shape: `s = 1.0 / len` under `len > 1e-20`
    // has no two-sided divisor interval (len's upper end is unbounded), yet
    // the floor gives the quotient the enclosure [-1e20, 1e20]; the product
    // `s * a` with `|a| <= 1e30` is then <= 1e50 and must discharge.
    let mut func = guarded_div(2, false, false, false);
    // Append `_5 = Mul(_4, a)` to the guarded block (local 5 is unused in
    // the non-copy-temp variant).
    func.body.blocks[1].stmts.push(assign(
        Place::local(5),
        Rvalue::BinaryOp(
            BinOp::Mul,
            Operand::Copy(Place::local(4)),
            Operand::Copy(Place::local(1)),
        ),
    ));
    assert!(v2_float_binop_cannot_overflow_at(
        &func,
        Some(BlockId(1)),
        None,
        BinOp::Mul,
        &Operand::Copy(Place::local(4)),
        &Operand::Copy(Place::local(1)),
    ));
}

#[test]
fn witness_magnitude_shapes_are_disjunctive_round11() {
    // Round-11 regression pin: the witness must OVER-approximate the
    // violation set. Add/Sub require AT LEAST ONE operand above MAX/2
    // (`MAX/4 + MAX` overflows with one small operand) — the magnitude
    // conjunct is an `Or`, never a per-operand `And` pair; Mul mirrors at
    // sqrt(MAX); Div carries NO numerator-magnitude conjunct at all
    // (`2.0 / 5e-324 = inf`). An And-shaped regression would let a
    // one-sided hypothesis (`|a| <= MAX/4`) prove UNSAT on a real
    // overflow.
    let func = guarded_div(2, false, false, false);
    let lhs = Operand::Copy(Place::local(1));
    let rhs = Operand::Copy(Place::local(2));
    for op in [BinOp::Add, BinOp::Sub] {
        let w =
            v2_float_overflow_witness_formula(&func, op, &lhs, &rhs).expect("witness minted");
        let Formula::And(conjuncts) = w else { panic!("{op:?} witness must be And") };
        assert!(
            conjuncts.iter().any(|c| matches!(c, Formula::Or(items) if items.len() == 2)),
            "{op:?} witness must carry the DISJUNCTIVE magnitude shape"
        );
    }
    let w = v2_float_overflow_witness_formula(&func, BinOp::Mul, &lhs, &rhs)
        .expect("witness minted");
    assert!(
        matches!(w, Formula::Or(ref items) if items.len() == 2),
        "Mul witness must be the two-operand disjunction"
    );
    let w = v2_float_overflow_witness_formula(&func, BinOp::Div, &lhs, &rhs)
        .expect("witness minted");
    let Formula::And(conjuncts) = w else { panic!("Div witness must be And") };
    assert_eq!(
        conjuncts.len(),
        2,
        "Div witness = divisor-magnitude + numerator-finite ONLY (no numerator magnitude)"
    );
}

#[test]
fn user_crate_trig_suffixes_are_not_unit_bounded() {
    // Round-13 false-proof pin: a USER function whose def-path merely ends
    // in `::cos`/`::sin`/`::tanh` (a truncated-Taylor `approx::cos`,
    // unbounded for large inputs) must NOT be granted the [-1, 1] interval
    // — only the crate-origin-anchored std methods qualify.
    for forged in [
        "mycrate::approx::cos",
        "mycrate::trig::sin",
        "mycrate::act::tanh",
        "mycrate::f64::cos_unchecked",
    ] {
        assert!(
            !super::is_unit_bounded_float_call(forged),
            "`{forged}` must not be unit-bounded"
        );
    }
    for genuine in ["std::f64::<impl f64>::cos", "core::f64::<impl f64>::sin"] {
        assert!(super::is_unit_bounded_float_call(genuine), "`{genuine}` must stay recognized");
    }
}

// =====================================================================
// Wave-3: F6b context-sensitive callee tracing, param overrides, per-
// field/enum hulls, abs-guard caps, and F7 contract hypotheses.
// =====================================================================

fn range_forbid_db(
    func: &VerifiableFunction,
    db: &SummaryDatabase,
    block: Option<BlockId>,
    operand: &Operand,
) -> Option<(f64, f64)> {
    let ctx = FloatRangeCtx::new(func, Some(db));
    float_range(
        &ctx,
        FloatNanMode::Forbid,
        block,
        operand,
        &mut Vec::new(),
        FLOAT_EXP_BOUND_FUEL,
    )
}

// ---- W3 item 2: caller-proved parameter-interval overrides ----

#[test]
fn param_override_bounds_defless_formal_read() {
    // f(a, b) { a - b } with NO contract: an override on `a` supplies the
    // entry fact; the un-overridden sibling stays unboundable.
    let func = sub_func(false);
    let mut ctx = FloatRangeCtx::new(&func, None);
    ctx.param_overrides.insert(1, (-2.0, 2.0));
    let read = |ctx: &FloatRangeCtx<'_>, local: usize| {
        float_range(
            ctx,
            FloatNanMode::Forbid,
            None,
            &Operand::Copy(Place::local(local)),
            &mut Vec::new(),
            FLOAT_EXP_BOUND_FUEL,
        )
    };
    assert_eq!(read(&ctx, 1), Some((-2.0, 2.0)));
    assert_eq!(read(&ctx, 2), None, "no override, no contract: fail-closed");
}

#[test]
fn param_override_is_ignored_for_reassigned_formal() {
    // SOUNDNESS twin: an override is an ENTRY fact — a formal with ANY
    // body write channel must not consume it (same discipline as contract
    // facts: the read may see the reassigned value OR the entry value).
    let func = make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("x")),
            decl(2, Ty::f64_ty(), Some("a")),
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(Place::local(1), Rvalue::Use(fconst(1.0))),
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(2)))),
            ],
            terminator: Terminator::Return,
        }],
        1,
        Ty::f64_ty(),
        vec![],
    );
    let mut ctx = FloatRangeCtx::new(&func, None);
    ctx.param_overrides.insert(1, (-2.0, 2.0));
    let r = float_range(
        &ctx,
        FloatNanMode::Forbid,
        None,
        &Operand::Copy(Place::local(1)),
        &mut Vec::new(),
        FLOAT_EXP_BOUND_FUEL,
    );
    assert_eq!(r, None, "a reassigned formal must never consume an entry override");
}

#[test]
fn malformed_param_override_is_refused() {
    let func = sub_func(false);
    for bad in [(f64::NAN, 2.0), (3.0, 2.0), (f64::NEG_INFINITY, 0.0), (0.0, f64::INFINITY)] {
        let mut ctx = FloatRangeCtx::new(&func, None);
        ctx.param_overrides.insert(1, bad);
        let r = float_range(
            &ctx,
            FloatNanMode::Forbid,
            None,
            &Operand::Copy(Place::local(1)),
            &mut Vec::new(),
            FLOAT_EXP_BOUND_FUEL,
        );
        assert_eq!(r, None, "malformed override {bad:?} must be refused");
    }
}

#[test]
fn param_override_is_consulted_before_the_contract() {
    // Both facts are valid entry facts; the callsite-specific override is
    // at least as tight and wins the lookup.
    let func = sub_func(true); // contract |a|,|b| <= 1e30
    let mut ctx = FloatRangeCtx::new(&func, None);
    ctx.param_overrides.insert(1, (-1.0, 1.0));
    let r = float_range(
        &ctx,
        FloatNanMode::Forbid,
        None,
        &Operand::Copy(Place::local(1)),
        &mut Vec::new(),
        FLOAT_EXP_BOUND_FUEL,
    );
    assert_eq!(r, Some((-1.0, 1.0)));
}

// ---- W3 items 1+3: context-sensitive callee tracing ----

/// `fn halve(v: f64) -> f64 { v * 0.5 }` — statically unboundable
/// (`v` has no contract), boundable only under a caller-derived override.
fn halve_callee(preconditions: Vec<Formula>) -> VerifiableFunction {
    make(
        vec![decl(0, Ty::f64_ty(), None), decl(1, Ty::f64_ty(), Some("v"))],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(0),
                Rvalue::BinaryOp(BinOp::Mul, Operand::Copy(Place::local(1)), fconst(0.5)),
            )],
            terminator: Terminator::Return,
        }],
        1,
        Ty::f64_ty(),
        preconditions,
    )
}

fn traced_leaf_db(callee: VerifiableFunction) -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    db.insert(
        FunctionSummary::new("leaf")
            .with_param_names(vec!["v".into()])
            .with_extracted_body(Arc::new(callee)),
    );
    db
}

#[test]
fn callee_trace_derives_a_context_sensitive_interval() {
    // The headline shape: the STATIC per-callee interval does not exist
    // (halve's formal is uncontracted, so `derive_float_result_range`
    // fails), yet at a call whose actual is caller-proved in [-2, 2] the
    // re-trace bounds the result near [-1, 1] — callsite-specific ranges
    // are exactly what the static summary cannot express.
    let callee = halve_callee(vec![]);
    assert_eq!(derive_float_result_range(&callee), None, "static lane must be stuck");
    let db = traced_leaf_db(callee);
    let caller = summary_caller(both("x", 2.0));
    let (lo, hi) =
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(2)))
            .expect("context-sensitive interval");
    assert!(lo <= -1.0 && lo >= -1.001 && hi >= 1.0 && hi <= 1.001, "got [{lo}, {hi}]");
    // …and the r*r Mul downstream discharges through it.
    assert!(mul_discharges_with(&caller, &db));
}

#[test]
fn callee_trace_without_a_caller_proved_actual_fails_closed() {
    // Adversarial twin: no caller contract → no override → the callee
    // read of `v` is unboundable → the whole trace refuses.
    let db = traced_leaf_db(halve_callee(vec![]));
    let caller = summary_caller(vec![]);
    assert_eq!(
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(2))),
        None
    );
    assert!(!mul_discharges_with(&caller, &db));
}

#[test]
fn callee_trace_requires_matching_extracted_arity() {
    // Adversarial twin: positional override binding is meaningless when
    // the extracted body's arity differs from the call — refuse.
    let mut callee = halve_callee(vec![]);
    callee.body.arg_count = 2;
    let db = traced_leaf_db(callee);
    let caller = summary_caller(both("x", 2.0));
    assert_eq!(
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(2))),
        None
    );
}

// ---- a3d `Aabb::center` replica: a struct chain whose SECOND callsite's
// actual is the FIRST call's dest (`self.min.add(self.max).scale(0.5)`).
// The add-callsite precondition discharges by direct F5 dominance (the
// actuals are deref'd param fields bounded by the caller contract); the
// scale-callsite one needs the F6b callee re-trace of `add`'s body under
// the caller-derived per-field overrides. Both must SUPPRESS — this is the
// exact production residual shape (48 unknowns in a3d-geom).

fn vec3_ty() -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        name: "Vec3".into(),
        fields: vec![
            ("x".into(), Ty::f64_ty()),
            ("y".into(), Ty::f64_ty()),
            ("z".into(), Ty::f64_ty()),
        ],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

fn aabb_ty() -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        name: "Aabb".into(),
        fields: vec![("min".into(), vec3_ty()), ("max".into(), vec3_ty())],
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

fn vec3_bounds(base: &str, c: f64) -> Vec<Formula> {
    (0..3)
        .flat_map(|i| {
            let name = format!("{base}.{i}");
            [le_f(&name, c), ge_f(&name, -c)]
        })
        .collect()
}

fn vec3_new_callee() -> VerifiableFunction {
    // fn new(x: f64, y: f64, z: f64) -> Vec3 { Vec3 { x, y, z } } — the
    // uncontracted per-field passthrough constructor (body-only summary).
    make(
        vec![
            decl(0, vec3_ty(), None),
            decl(1, Ty::f64_ty(), None),
            decl(2, Ty::f64_ty(), None),
            decl(3, Ty::f64_ty(), None),
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(0),
                Rvalue::Aggregate(
                    AggregateKind::Adt { name: "Vec3".into(), variant: 0, active_field: None, args: None },
                    vec![
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                        Operand::Copy(Place::local(3)),
                    ],
                ),
            )],
            terminator: Terminator::Return,
        }],
        3,
        vec3_ty(),
        vec![],
    )
}

fn vec3_add_callee() -> VerifiableFunction {
    // PRODUCTION shape: fn add(self: Vec3, o: Vec3) -> Vec3 {
    //   Vec3::new(self.x + o.x, self.y + o.y, self.z + o.z)
    // } — the result flows through the nested `Vec3::new` CALL (the trace
    // must recurse through new's body-only summary), not a direct
    // aggregate.
    let mut pre = vec3_bounds("self", 1.0e150);
    pre.extend(vec3_bounds("o", 1.0e150));
    make(
        vec![
            decl(0, vec3_ty(), None),
            decl(1, vec3_ty(), Some("self")),
            decl(2, vec3_ty(), Some("o")),
            decl(3, Ty::f64_ty(), None),
            decl(4, Ty::f64_ty(), None),
            decl(5, Ty::f64_ty(), None),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(
                        Place::local(3),
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::field(1, 0)),
                            Operand::Copy(Place::field(2, 0)),
                        ),
                    ),
                    assign(
                        Place::local(4),
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::field(1, 1)),
                            Operand::Copy(Place::field(2, 1)),
                        ),
                    ),
                    assign(
                        Place::local(5),
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::field(1, 2)),
                            Operand::Copy(Place::field(2, 2)),
                        ),
                    ),
                ],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "Vec3::new".to_string(),
                    args: vec![
                        Operand::Move(Place::local(3)),
                        Operand::Move(Place::local(4)),
                        Operand::Move(Place::local(5)),
                    ],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
        vec3_ty(),
        vec![Formula::And(pre)],
    )
}

fn center_caller() -> VerifiableFunction {
    // fn center(&self: &Aabb) -> Vec3, requires |self.min.*|,|self.max.*| <= 1e149:
    //   _2 = (*_1).0; _3 = (*_1).1; _4 = add(_2, _3); _5 = scale(_4, 0.5); _0 = _5
    let deref_field = |f: usize| Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Field(f)],
    };
    let mut pre: Vec<Formula> = Vec::new();
    for (fld, base) in [(0, "self*.0"), (1, "self*.1")] {
        let _ = fld;
        for i in 0..3 {
            let name = format!("{base}.{i}");
            pre.push(le_f(&name, 1.0e149));
            pre.push(ge_f(&name, -1.0e149));
        }
    }
    make(
        vec![
            decl(0, vec3_ty(), None),
            decl(1, Ty::Ref { mutable: false, inner: Box::new(aabb_ty()) }, Some("self")),
            decl(2, vec3_ty(), None),
            decl(3, vec3_ty(), None),
            decl(4, vec3_ty(), None),
            decl(5, vec3_ty(), None),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(Place::local(2), Rvalue::Use(Operand::Copy(deref_field(0)))),
                    assign(Place::local(3), Rvalue::Use(Operand::Copy(deref_field(1)))),
                ],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "Vec3::add".to_string(),
                    args: vec![
                        Operand::Copy(Place::local(2)),
                        Operand::Copy(Place::local(3)),
                    ],
                    dest: Place::local(4),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "Vec3::scale".to_string(),
                    args: vec![Operand::Move(Place::local(4)), fconst(0.5)],
                    dest: Place::local(5),
                    target: Some(BlockId(2)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(5))))],
                terminator: Terminator::Return,
            },
        ],
        1,
        vec3_ty(),
        vec![Formula::And(pre)],
    )
}

fn center_chain_db() -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    // Body-only summary for the uncontracted `Vec3::new` passthrough (the
    // wave-3 contract-less-callee case — production attaches these too).
    db.insert(
        FunctionSummary::new("Vec3::new")
            .with_param_names(vec!["_1".into(), "_2".into(), "_3".into()])
            .with_extracted_body(Arc::new(vec3_new_callee())),
    );
    let mut add_pre = vec3_bounds("self", 1.0e150);
    add_pre.extend(vec3_bounds("o", 1.0e150));
    let mut add = FunctionSummary::new("Vec3::add")
        .with_param_names(vec!["self".into(), "o".into()])
        .with_extracted_body(Arc::new(vec3_add_callee()));
    add = add.with_precondition(Formula::And(add_pre));
    db.insert(add);
    let mut scale_pre = vec3_bounds("self", 1.0e150);
    scale_pre.push(le_f("s", 1.0e150));
    scale_pre.push(ge_f("s", -1.0e150));
    let mut scale = FunctionSummary::new("Vec3::scale")
        .with_param_names(vec!["self".into(), "s".into()]);
    scale = scale.with_precondition(Formula::And(scale_pre));
    db.insert(scale);
    db
}

fn load_center_fixture(name: &str) -> VerifiableFunction {
    let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/center-chain-2026-07-18")
        .join(format!("{name}.json"));
    serde_json::from_slice(&std::fs::read(p).expect("fixture present")).expect("parse")
}

#[test]
fn center_chain_production_dump_suppresses_both_precondition_vcs() {
    // GROUND TRUTH: byte-for-byte `-Ztrust-dump=mir:<dir>` dumps of the real
    // compiler extraction (see fixtures/center-chain-2026-07-18/
    // PROVENANCE.md) with the summary db assembled exactly as
    // `add_direct_call_contract_summaries` does (names/params/preconds
    // from the probe of the same build). The hand-built replica below
    // passes while PRODUCTION mints the scale-callsite VC — this test
    // reproduces the production inputs so the divergence is pinned and
    // fixed in-crate.
    let center = load_center_fixture("center");
    let add = load_center_fixture("add");
    let scale = load_center_fixture("scale");
    let new = load_center_fixture("new");

    let mut db = SummaryDatabase::new();
    // Post-wave-4 production db: the compiler's transitive trace closure
    // registers `Vec3::new` (add's callee) as a body-only summary.
    db.insert(
        FunctionSummary::new("Vec3::new")
            .with_param_names(vec!["_1".into(), "_2".into(), "_3".into()])
            .with_extracted_body(Arc::new(new)),
    );
    let mut add_summary = FunctionSummary::new("Vec3::add")
        .with_param_names(vec!["self".into(), "o".into()])
        .with_extracted_body(Arc::new(add.clone()));
    for pre in &add.preconditions {
        add_summary = add_summary.with_precondition(pre.clone());
    }
    db.insert(add_summary);
    let mut scale_summary = FunctionSummary::new("Vec3::scale")
        .with_param_names(vec!["self".into(), "s".into()])
        .with_extracted_body(Arc::new(scale.clone()));
    for pre in &scale.preconditions {
        scale_summary = scale_summary.with_precondition(pre.clone());
    }
    db.insert(scale_summary);

    let vcs = generate_callsite_precondition_vcs(&center, &db);
    let pre: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
        .collect();
    assert!(
        pre.is_empty(),
        "the production center chain must discharge both callsites, got {} VC(s): {:?}",
        pre.len(),
        pre.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

fn load_mat_fixture(name: &str) -> VerifiableFunction {
    let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/mat-chain-2026-07-18")
        .join(format!("{name}.json"));
    serde_json::from_slice(&std::fs::read(p).expect("fixture present")).expect("parse")
}

#[test]
fn mat_chain_row_dot_production_dump_suppresses_the_dot_precondition() {
    // GROUND TRUTH for the remaining a3d-geom residual class (Vec4::dot
    // chains in mul_mat4/transform_*): `mul_row = self.row(0).dot(v)`.
    // `row` is a 4-arm match; each arm bounds-asserts its constant
    // column reads and calls `Vec4::new` with dest `_0` — so the
    // dot-callsite actual (`row(0)`'s dest) traces through a MULTI-DEF
    // hull over four CALL-dest defs, each through the transitive
    // `Vec4::new` passthrough, all bounded by `mul_row`'s own per-element
    // contract (F5 dominance closes the whole obligation).
    let mul_row = load_mat_fixture("mul_row");
    let row = load_mat_fixture("row");
    let dot = load_mat_fixture("dot");
    let new = load_mat_fixture("new");

    let mut db = SummaryDatabase::new();
    db.insert(
        FunctionSummary::new("Vec4::new")
            .with_param_names(vec![
                "_1".into(),
                "_2".into(),
                "_3".into(),
                "_4".into(),
            ])
            .with_extracted_body(Arc::new(new)),
    );
    let mut row_summary = FunctionSummary::new("Mat2::row")
        .with_param_names(vec!["self".into(), "r".into()])
        .with_extracted_body(Arc::new(row.clone()));
    for pre in &row.preconditions {
        row_summary = row_summary.with_precondition(pre.clone());
    }
    db.insert(row_summary);
    let mut dot_summary = FunctionSummary::new("Vec4::dot")
        .with_param_names(vec!["self".into(), "o".into()])
        .with_extracted_body(Arc::new(dot.clone()));
    for pre in &dot.preconditions {
        dot_summary = dot_summary.with_precondition(pre.clone());
    }
    db.insert(dot_summary);

    let vcs = generate_callsite_precondition_vcs(&mul_row, &db);
    let pre: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
        .collect();
    assert!(
        pre.is_empty(),
        "the row(0).dot(v) chain must discharge, got {} VC(s): {:?}",
        pre.len(),
        pre.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

fn load_deep_fixture(name: &str) -> VerifiableFunction {
    let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/deep-chain-2026-07-18")
        .join(format!("{name}.json"));
    serde_json::from_slice(&std::fs::read(p).expect("fixture present")).expect("parse")
}

#[test]
fn deep_chain_through_normalized_division_suppresses_the_dot_precondition() {
    // GROUND TRUTH for the final a3d-geom residual class (look_at chains):
    // `forward_dot = at.sub(eye).normalized().dot(at)` — the dot-callsite
    // actual traces through `normalized`'s body, whose result fields pass
    // through a GUARDED DIVISION (`len > 1e-20` floor over a <= 1e50
    // numerator gives fields <= 1e70 <= dot's 1e100 requirement).
    let fwd = load_deep_fixture("forward_dot");
    let sub = load_deep_fixture("sub");
    let normalized = load_deep_fixture("normalized");
    let dot = load_deep_fixture("dot");
    let new = load_deep_fixture("new");

    let mut db = SummaryDatabase::new();
    db.insert(
        FunctionSummary::new("Vec3::new")
            .with_param_names(vec!["_1".into(), "_2".into(), "_3".into()])
            .with_extracted_body(Arc::new(new)),
    );
    for (name, f) in [
        ("Vec3::sub", &sub),
        ("Vec3::normalized", &normalized),
        ("Vec3::dot", &dot),
    ] {
        let params: Vec<String> = if f.body.arg_count == 1 {
            vec!["self".into()]
        } else {
            vec!["self".into(), "o".into()]
        };
        let mut s = FunctionSummary::new(name)
            .with_param_names(params)
            .with_extracted_body(Arc::new(f.clone()));
        for pre in &f.preconditions {
            s = s.with_precondition(pre.clone());
        }
        db.insert(s);
    }

    let vcs = generate_callsite_precondition_vcs(&fwd, &db);
    let pre: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
        .collect();
    assert!(
        pre.is_empty(),
        "the sub→normalized→dot chain must discharge, got {} VC(s): {:?}",
        pre.len(),
        pre.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

#[test]
fn deep_chain_guarded_division_emits_no_float_div_obligation() {
    // The transform_point Div class: `p.x / w` under `w.abs() > 1e-20`
    // with `|p.x| <= 1e50` — quotient <= 1e70, under the 2^1020 margin;
    // the abs-guard floor + contract cap must discharge the
    // FloatOverflowToInfinity(Div) obligations inside half_point itself.
    let half = load_deep_fixture("half_point");
    let vcs = generate_v2_safety_vcs(&half);
    let float_divs: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::FloatOverflowToInfinity { op: BinOp::Div, .. })
        })
        .collect();
    assert!(
        float_divs.is_empty(),
        "the guarded division must discharge, got {} Div VC(s)",
        float_divs.len()
    );
}

#[test]
fn a3d_geom_whole_crate_residual_diagnosis() {
    // Whole-crate harness over the real a3d-geom dumps: build the
    // production-equivalent summary db (every function, keyed by
    // def_path == the callers' call-string, with preconditions + body)
    // and report which callsite-precondition VCs still mint for the
    // residual functions. Diagnostic: prints the census; asserts only
    // that the harness ran (the numeric goal is tracked outside).
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/a3d-geom-2026-07-18");
    let mut db = SummaryDatabase::new();
    let mut fns: Vec<VerifiableFunction> = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("fixture dir") {
        let p = entry.expect("entry").path();
        if p.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let raw = std::fs::read_to_string(&p).expect("read");
        // Mat4-class contracts nest ~64 `And` levels — use the
        // depth-tolerant parser (the same one the compiler uses for VC
        // payloads).
        let f: VerifiableFunction =
            trust_types::json_depth::from_str_deep(&raw).expect("parse");
        fns.push(f);
    }
    for f in &fns {
        let arg_count = f.body.arg_count;
        let params: Vec<String> = (1..=arg_count)
            .map(|i| {
                f.body
                    .locals
                    .get(i)
                    .and_then(|l| l.name.clone())
                    .unwrap_or_else(|| format!("_{i}"))
            })
            .collect();
        let mut s = FunctionSummary::new(f.def_path.clone())
            .with_param_names(params)
            .with_extracted_body(Arc::new(f.clone()));
        for pre in &f.preconditions {
            s = s.with_precondition(pre.clone());
        }
        db.insert(s);
    }
    let mut total = 0usize;
    for f in &fns {
        let vcs = generate_callsite_precondition_vcs(f, &db);
        let minted: Vec<String> = vcs
            .iter()
            .filter_map(|vc| match &vc.kind {
                VcKind::Precondition { callee } => Some(callee.clone()),
                _ => None,
            })
            .collect();
        if !minted.is_empty() {
            total += minted.len();
            eprintln!("[A3D-DIAG] {} mints {}: {:?}", f.def_path, minted.len(), minted);
        }
    }
    eprintln!("[A3D-DIAG] TOTAL precondition VCs minted crate-wide: {total}");
    // Regression guard: driven to ZERO across a sequence of tracer lanes —
    // batch-3 + trace-memo (21→12), the interproc-fuel raise 16→32 (12→4,
    // the deep `Vec3::add(rotate(..))` chains in compose/transform_point),
    // the abs-guard-arg copy-source canonicalization (4→3, inverse's
    // `1.0/self.scale` scale factor), and the flow-sensitive masked-init lane
    // + const-index resolution (3→0, to_mat4's `m.cols[k]` reads of a
    // mutated-in-place local). EVERY a3d-geom callsite precondition now
    // discharges. A REGRESSION above 0 means a trace lane broke.
    assert_eq!(
        total, 0,
        "a3d-geom crate-wide precondition-VC residual regressed to {total} (expected 0)"
    );
}

#[test]
fn mat_chain_soundness_twins() {
    let mul_row = load_mat_fixture("mul_row");
    let row = load_mat_fixture("row");
    let dot = load_mat_fixture("dot");
    let new = load_mat_fixture("new");

    // (a) WITHOUT the transitive Vec4::new summary the multi-Call hull's
    // inner traces refuse and the dot VC mints (fail-closed absence).
    let mut db = SummaryDatabase::new();
    let mut row_summary = FunctionSummary::new("Mat2::row")
        .with_param_names(vec!["self".into(), "r".into()])
        .with_extracted_body(Arc::new(row.clone()));
    for pre in &row.preconditions {
        row_summary = row_summary.with_precondition(pre.clone());
    }
    db.insert(row_summary.clone());
    let mut dot_summary = FunctionSummary::new("Vec4::dot")
        .with_param_names(vec!["self".into(), "o".into()])
        .with_extracted_body(Arc::new(dot.clone()));
    for pre in &dot.preconditions {
        dot_summary = dot_summary.with_precondition(pre.clone());
    }
    db.insert(dot_summary.clone());
    let vcs = generate_callsite_precondition_vcs(&mul_row, &db);
    assert!(
        vcs.iter().any(
            |vc| matches!(&vc.kind, VcKind::Precondition { callee } if callee == "Vec4::dot")
        ),
        "missing transitive new must keep the dot VC minted: {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );

    // (b) INT-lane soundness twin: replace row's auto type-range requires
    // with a NON-tautological int bound (`r <= 2`); the callsite passes a
    // CONSTANT 0 which satisfies it — still discharges — but a bound the
    // constant VIOLATES (`r >= 1` with actual 0) must mint.
    let mut tight = FunctionSummary::new("Mat2::row")
        .with_param_names(vec!["self".into(), "r".into()])
        .with_extracted_body(Arc::new(row.clone()));
    for pre in &row.preconditions {
        tight = tight.with_precondition(pre.clone());
    }
    tight = tight.with_precondition(Formula::Ge(
        Box::new(Formula::Var("r".to_string(), Sort::Int)),
        Box::new(Formula::Int(1)),
    ));
    let mut db2 = SummaryDatabase::new();
    db2.insert(
        FunctionSummary::new("Vec4::new")
            .with_param_names(vec!["_1".into(), "_2".into(), "_3".into(), "_4".into()])
            .with_extracted_body(Arc::new(new)),
    );
    db2.insert(tight);
    db2.insert(dot_summary);
    let vcs = generate_callsite_precondition_vcs(&mul_row, &db2);
    assert!(
        vcs.iter().any(
            |vc| matches!(&vc.kind, VcKind::Precondition { callee } if callee == "Mat2::row")
        ),
        "a violated int precondition (r >= 1, actual 0) must mint: {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

#[test]
fn center_chain_without_transitive_callee_summary_mints_the_scale_vc() {
    // The load-bearing WHY of the compiler's wave-4 transitive trace
    // closure: with `Vec3::new` (add's transitive callee) ABSENT from the
    // db — exactly the pre-wave-4 production db, which registered the
    // caller's DIRECT callees only — the re-trace through `add`'s body
    // dies at the un-summarized `Vec3::new` call and the scale-callsite
    // precondition VC is minted (the a3d-geom struct-chain residual). The
    // add-callsite still F5-discharges (param-rooted actuals need no
    // trace). Fail-closed: absence mints, never falsely suppresses.
    let center = load_center_fixture("center");
    let add = load_center_fixture("add");
    let scale = load_center_fixture("scale");

    let mut db = SummaryDatabase::new();
    let mut add_summary = FunctionSummary::new("Vec3::add")
        .with_param_names(vec!["self".into(), "o".into()])
        .with_extracted_body(Arc::new(add.clone()));
    for pre in &add.preconditions {
        add_summary = add_summary.with_precondition(pre.clone());
    }
    db.insert(add_summary);
    let mut scale_summary = FunctionSummary::new("Vec3::scale")
        .with_param_names(vec!["self".into(), "s".into()])
        .with_extracted_body(Arc::new(scale.clone()));
    for pre in &scale.preconditions {
        scale_summary = scale_summary.with_precondition(pre.clone());
    }
    db.insert(scale_summary);

    let vcs = generate_callsite_precondition_vcs(&center, &db);
    let pre: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
        .collect();
    assert_eq!(pre.len(), 1, "exactly the scale callsite must mint: {pre:?}");
    assert!(
        matches!(&pre[0].kind, VcKind::Precondition { callee } if callee == "Vec3::scale"),
        "{:?}",
        pre[0].kind
    );
}

#[test]
fn center_chain_call_dest_actual_suppresses_both_precondition_vcs() {
    let caller = center_caller();
    let db = center_chain_db();
    let vcs = generate_callsite_precondition_vcs(&caller, &db);
    let pre: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
        .collect();
    assert!(
        pre.is_empty(),
        "both chain callsites must discharge structurally (F5 + F6b), got {} VC(s): {:?}",
        pre.len(),
        pre.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
    // The ATTRIBUTED twin (the PRODUCTION entry point — trust_verify calls
    // this one) must suppress identically.
    let attributed = generate_callsite_precondition_vcs_attributed(&caller, &db);
    assert!(
        attributed.is_empty(),
        "the attributed twin must suppress the same chain, got {} VC(s)",
        attributed.len()
    );
}

#[test]
fn callee_trace_reestablishes_the_callee_preconditions() {
    // The re-trace consumes the body's own gated preconditions
    // (`contract_range` inside the callee), so they must be structurally
    // re-established at the call (assume-guarantee, the F6 discipline):
    // |v| <= 1 required, caller only proves |x| <= 2 → REFUSE…
    let db = traced_leaf_db(halve_callee(both("v", 1.0)));
    let wide_caller = summary_caller(both("x", 2.0));
    assert_eq!(
        range_forbid_db(&wide_caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(2))),
        None,
        "an unestablished callee precondition must refuse the trace"
    );
    // …while a caller proving |x| <= 1 re-establishes it and traces.
    let tight_caller = summary_caller(both("x", 1.0));
    let (lo, hi) =
        range_forbid_db(&tight_caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(2)))
            .expect("dominated precondition unlocks the trace");
    assert!(lo <= -0.5 && lo >= -0.51 && hi >= 0.5 && hi <= 0.51, "got [{lo}, {hi}]");
}

/// `fn f() -> f64 { <callee>() }` — a zero-arg forwarder (also used as the
/// zero-arg caller shape: read the dest at bb1).
fn forwarder(callee: &str) -> VerifiableFunction {
    make(
        vec![decl(0, Ty::f64_ty(), None), decl(1, Ty::f64_ty(), None)],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: callee.to_string(),
                    args: vec![],
                    dest: Place::local(1),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::Use(Operand::Copy(Place::local(1))),
                )],
                terminator: Terminator::Return,
            },
        ],
        0,
        Ty::f64_ty(),
        vec![],
    )
}

fn const_leaf() -> VerifiableFunction {
    make(
        vec![decl(0, Ty::f64_ty(), None)],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(Place::local(0), Rvalue::Use(fconst(1.0)))],
            terminator: Terminator::Return,
        }],
        0,
        Ty::f64_ty(),
        vec![],
    )
}

fn body_summary(name: &str, body: VerifiableFunction) -> FunctionSummary {
    FunctionSummary::new(name).with_extracted_body(Arc::new(body))
}

#[test]
fn callee_trace_depth_is_limited_to_three() {
    // c1 -> c2 -> c3(=const) traces; adding a fourth level refuses.
    let mut db = SummaryDatabase::new();
    db.insert(body_summary("c1", forwarder("c2")));
    db.insert(body_summary("c2", forwarder("c3")));
    db.insert(body_summary("c3", const_leaf()));
    let caller = forwarder("c1");
    assert_eq!(
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(1))),
        Some((1.0, 1.0)),
        "a 3-deep chain is within the interprocedural budget"
    );
    let mut db = SummaryDatabase::new();
    db.insert(body_summary("c1", forwarder("c2")));
    db.insert(body_summary("c2", forwarder("c3")));
    db.insert(body_summary("c3", forwarder("c4")));
    db.insert(body_summary("c4", const_leaf()));
    assert_eq!(
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(1))),
        None,
        "the 4th nesting level must be refused (fail-closed)"
    );
}

#[test]
fn callee_trace_recursion_is_cut_by_the_visiting_stack() {
    // `rec()` whose extracted body calls `rec` again: the shared callee
    // stack refuses the nested trace, and the refusal propagates.
    let mut db = SummaryDatabase::new();
    db.insert(body_summary("rec", forwarder("rec")));
    let caller = forwarder("rec");
    assert_eq!(
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(1))),
        None
    );
}

// ---- W3 item 3 (per-suffix) + item 4 (Option payload / Use rebase) ----

/// `fn mk(v: f64) -> (f64, f64) { (v, 7.0) }` — a struct return, invisible
/// to scalar F6 (`derive_float_result_range` hard-gates on f64 returns).
fn pair_callee() -> VerifiableFunction {
    let tuple_ty = Ty::Tuple(vec![Ty::f64_ty(), Ty::f64_ty()]);
    make(
        vec![decl(0, tuple_ty.clone(), None), decl(1, Ty::f64_ty(), Some("v"))],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(0),
                Rvalue::Aggregate(
                    AggregateKind::Tuple,
                    vec![Operand::Copy(Place::local(1)), fconst(7.0)],
                ),
            )],
            terminator: Terminator::Return,
        }],
        1,
        tuple_ty,
        vec![],
    )
}

/// `t = leaf(x); read t.<k>` with an optional caller contract on `x`.
fn pair_caller(pre: Vec<Formula>) -> VerifiableFunction {
    let tuple_ty = Ty::Tuple(vec![Ty::f64_ty(), Ty::f64_ty()]);
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("x")),
            decl(2, tuple_ty, Some("t")),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "leaf".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(2),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::Use(Operand::Copy(Place::field(2, 0))),
                )],
                terminator: Terminator::Return,
            },
        ],
        1,
        Ty::f64_ty(),
        pre,
    )
}

#[test]
fn call_dest_field_read_traces_through_the_extracted_body() {
    // Per-suffix consumption: `t.0` re-traces `_0.0` (the passthrough
    // formal under the caller-proved override), `t.1` re-traces `_0.1`
    // (the frozen literal). Scalar F6 can express neither.
    let callee = pair_callee();
    assert_eq!(derive_float_result_range(&callee), None, "struct return: scalar F6 is out");
    let db = traced_leaf_db(callee);
    let caller = pair_caller(both("x", 2.0));
    assert_eq!(
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::field(2, 0))),
        Some((-2.0, 2.0))
    );
    assert_eq!(
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::field(2, 1))),
        Some((7.0, 7.0))
    );
    // Adversarial: a field the callee never constructs refuses.
    let bogus = Place { local: 2, projections: vec![Projection::Field(9)] };
    assert_eq!(range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(bogus)), None);
}

fn option_kind(variant: usize) -> AggregateKind {
    AggregateKind::Adt { name: "core::option::Option".into(), variant, active_field: None, args: None }
}

/// `fn maybe(v: f64, c: bool) -> Option<f64>`-shaped callee: the Some arm
/// (variant 1) carries `v * 0.5`, the None arm (variant 0) is empty —
/// exactly the two-def `_0` shape `Vec3::normalized` extracts to.
/// `via_copy`: the Some arm builds into a temp and whole-local-copies it
/// to `_0` (the collector must recurse). `none_only`: both arms build
/// variant 0 (a `@1` read is then never defined). `call_def`: the Some arm
/// is an opaque Call dest (must poison the collection).
fn option_callee(via_copy: bool, none_only: bool, call_def: bool) -> VerifiableFunction {
    let some_stmts = if none_only {
        vec![assign(Place::local(0), Rvalue::Aggregate(option_kind(0), vec![]))]
    } else if via_copy {
        vec![
            assign(
                Place::local(4),
                Rvalue::Aggregate(option_kind(1), vec![Operand::Copy(Place::local(3))]),
            ),
            assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(4)))),
        ]
    } else {
        vec![assign(
            Place::local(0),
            Rvalue::Aggregate(option_kind(1), vec![Operand::Copy(Place::local(3))]),
        )]
    };
    let some_block = if call_def {
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: trust_types::UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                is_foreign: false,
                func: "mystery".to_string(),
                args: vec![],
                dest: Place::local(0),
                target: Some(BlockId(3)),
                span: SourceSpan::default(),
                atomic: None,
            },
        }
    } else {
        BasicBlock {
            id: BlockId(1),
            stmts: some_stmts,
            terminator: Terminator::Goto(BlockId(3)),
        }
    };
    make(
        vec![
            decl(0, Ty::Unit, None), // enum-typed; the tracer never consults it
            decl(1, Ty::f64_ty(), Some("v")),
            decl(2, Ty::Bool, Some("c")),
            decl(3, Ty::f64_ty(), None),
            decl(4, Ty::Unit, None),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    Place::local(3),
                    Rvalue::BinaryOp(BinOp::Mul, Operand::Copy(Place::local(1)), fconst(0.5)),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            some_block,
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(Place::local(0), Rvalue::Aggregate(option_kind(0), vec![]))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
        Ty::Unit,
        vec![],
    )
}

/// `o = leaf(x, flag); _4 = copy o@1.0; read _4` — the exact extracted
/// caller shape from the MIR probe (payload hops through a Use temp).
fn option_caller(pre: Vec<Formula>) -> VerifiableFunction {
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("x")),
            decl(2, Ty::Bool, Some("flag")),
            decl(3, Ty::Unit, Some("o")),
            decl(4, Ty::f64_ty(), None),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "leaf".to_string(),
                    args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    dest: Place::local(3),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    assign(
                        Place::local(4),
                        Rvalue::Use(Operand::Copy(Place {
                            local: 3,
                            projections: vec![Projection::Downcast(1), Projection::Field(0)],
                        })),
                    ),
                    assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(4)))),
                ],
                terminator: Terminator::Return,
            },
        ],
        2,
        Ty::f64_ty(),
        pre,
    )
}

fn option_db(callee: VerifiableFunction) -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    db.insert(body_summary("leaf", callee));
    db
}

#[test]
fn option_payload_read_hulls_only_the_matching_variant_defs() {
    // Caller side: the Downcast place hops through a Use temp (`_4 = copy
    // o@1.0`), resolved by the whole-local Use recursion. Callee side: the
    // `@1.0` read selects the variant-1 construction def ONLY (the
    // variant-0 def carries no payload and no license — a Downcast(1)
    // read is defined only when the discriminant IS 1, and the value then
    // comes from a variant-1 def).
    let db = option_db(option_callee(false, false, false));
    let caller = option_caller(both("x", 2.0));
    let (lo, hi) =
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(4)))
            .expect("payload interval");
    assert!(lo <= -1.0 && lo >= -1.001 && hi >= 1.0 && hi <= 1.001, "got [{lo}, {hi}]");
}

#[test]
fn option_payload_collector_recurses_through_whole_local_copies() {
    // The Some arm builds into `_4` and copies it whole to `_0` — the
    // construction-def collector must flatten through the copy.
    let db = option_db(option_callee(true, false, false));
    let caller = option_caller(both("x", 2.0));
    let (lo, hi) =
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(4)))
            .expect("payload interval through the copy hop");
    assert!(lo <= -1.0 && hi >= 1.0 && hi <= 1.001, "got [{lo}, {hi}]");
}

#[test]
fn option_payload_without_a_matching_variant_def_fails_closed() {
    // Adversarial twin: every def is variant 0 — a `@1` read is never
    // DEFINED, so no claim may be made.
    let db = option_db(option_callee(false, true, false));
    let caller = option_caller(both("x", 2.0));
    assert_eq!(
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(4))),
        None
    );
}

#[test]
fn option_payload_with_an_opaque_def_in_the_set_fails_closed() {
    // Adversarial twin: one `_0` def is a Call — the value model over
    // construction defs no longer covers every read; refuse everything.
    let db = option_db(option_callee(false, false, true));
    let caller = option_caller(both("x", 2.0));
    assert_eq!(
        range_forbid_db(&caller, &db, Some(BlockId(1)), &Operand::Copy(Place::local(4))),
        None
    );
}

// ---- W3 item 4 (caller side): unique-Use-def projection rebase ----

#[test]
fn use_temp_field_read_rebases_onto_the_contract_chain() {
    // w3recon-1 Q6 (the Aabb add/sub missing link): `_2 = copy (a.0);
    // read _2.1` must rebase to the admitted depth-2 chain `a.0.1`.
    let inner_ty = Ty::Tuple(vec![Ty::f64_ty(), Ty::f64_ty()]);
    let outer_ty = Ty::Tuple(vec![inner_ty.clone()]);
    let func = make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, outer_ty, Some("a")),
            decl(2, inner_ty, None),
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::field(1, 0)))),
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::field(2, 1)))),
            ],
            terminator: Terminator::Return,
        }],
        1,
        Ty::f64_ty(),
        both("a.0.1", 1e10),
    );
    assert_eq!(
        range_forbid(&func, None, &Operand::Copy(Place::field(2, 1))),
        Some((-1e10, 1e10))
    );
    // A SECOND identical copy def is now SOUNDLY hulled (the mixed
    // multi-def hull): both defs are `_2 = copy(a.0)`, so a read of `_2.1`
    // yields `a.0.1` on EITHER reaching def — the hull over both is the
    // same admitted `a.0.1` range. (Formerly refused by the single-def
    // rebase lane's conservatism; the reused-slot case — `look_at_rh`'s
    // basis vectors — is exactly this shape.)
    let mut two_defs = func.clone();
    two_defs.body.blocks[0].stmts.insert(
        1,
        assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::field(1, 0)))),
    );
    assert_eq!(
        range_forbid(&two_defs, None, &Operand::Copy(Place::field(2, 1))),
        Some((-1e10, 1e10))
    );
    // SOUNDNESS twin: one def copies the CONTRACTED chain, the other copies
    // an UNCONTRACTED local — the hull must refuse (that def is unboundable,
    // so a read on its path is unbounded). Fail-closed: ANY untraceable def
    // poisons the whole hull.
    let mut mixed = func.clone();
    mixed.body.locals.push(decl(3, Ty::Tuple(vec![Ty::f64_ty(), Ty::f64_ty()]), Some("u")));
    mixed.body.blocks[0].stmts.insert(
        1,
        assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(3)))),
    );
    assert_eq!(range_forbid(&mixed, None, &Operand::Copy(Place::field(2, 1))), None);
}

#[test]
fn compose_scalar_field_actual_dominates_through_copy_temps() {
    // w3recon-5 surprise 3 (the compose mystery, reproduced): the scale
    // callsite's actuals are BOTH copy temps of entry-stable param fields
    // (`_3 = copy inner.0` a struct field, `_4 = copy self.2` a scalar
    // field). The callee precondition var `self.0` maps onto `_3.0`, which
    // only resolves through the unique-Use-def rebase (`_3.0 -> inner.0.0`)
    // — precisely the gap that kept `inner.translation.scale(self.scale)`
    // L0-unknown while `.scale(0.5)` went clean.
    let vec1 = Ty::Tuple(vec![Ty::f64_ty()]);
    let selfish = Ty::Tuple(vec![Ty::f64_ty(), Ty::f64_ty(), Ty::f64_ty()]);
    let inner_ty = Ty::Tuple(vec![vec1.clone()]);
    let build = |pre: Vec<Formula>| {
        make(
            vec![
                decl(0, Ty::Unit, None),
                decl(1, selfish.clone(), Some("self")),
                decl(2, inner_ty.clone(), Some("inner")),
                decl(3, vec1.clone(), None),
                decl(4, Ty::f64_ty(), None),
                decl(5, vec1.clone(), None),
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::field(2, 0)))),
                        assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::field(1, 2)))),
                    ],
                    terminator: Terminator::Call {
                        unwind: trust_types::UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "scale".to_string(),
                        args: vec![
                            Operand::Move(Place::local(3)),
                            Operand::Move(Place::local(4)),
                        ],
                        dest: Place::local(5),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            2,
            Ty::Unit,
            pre,
        )
    };
    let mut db = SummaryDatabase::new();
    db.insert(
        FunctionSummary::new("scale")
            .with_param_names(vec!["self".into(), "s".into()])
            .with_precondition(Formula::And(vec![
                le_f("self.0", 1e150),
                ge_f("self.0", -1e150),
                le_f("s", 1e150),
                ge_f("s", -1e150),
            ])),
    );
    let mut pre = both("inner.0.0", 1e100);
    pre.extend(both("self.2", 1.0));
    let vcs = generate_callsite_precondition_vcs(&build(pre), &db);
    assert!(vcs.is_empty(), "both actual chains dominate — no obligation: {vcs:?}");
    // Adversarial twin: without the caller's vector-field chain contract
    // the `self.0` conjunct cannot be established — the obligation stays.
    let vcs = generate_callsite_precondition_vcs(&build(both("self.2", 1.0)), &db);
    assert_eq!(vcs.len(), 1, "undominated precondition must keep its VC");
}

// ---- W3 item 5: multi-def aggregate per-field hull ----

/// `if c { q = Tuple(1.0, 2.0) } else { q = <kind>(second) }; read q.k`.
fn branchy_pair(second_kind: AggregateKind, second: Vec<Operand>) -> VerifiableFunction {
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::Bool, Some("c")),
            decl(2, Ty::f64_ty(), Some("x")),
            decl(3, Ty::Tuple(vec![Ty::f64_ty(), Ty::f64_ty()]), Some("q")),
        ],
        vec![
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
                stmts: vec![assign(
                    Place::local(3),
                    Rvalue::Aggregate(AggregateKind::Tuple, vec![fconst(1.0), fconst(2.0)]),
                )],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(Place::local(3), Rvalue::Aggregate(second_kind, second))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                )],
                terminator: Terminator::Return,
            },
        ],
        2,
        Ty::f64_ty(),
        vec![],
    )
}

#[test]
fn multi_def_aggregate_per_field_hull() {
    // The `from_basis` shape: two same-shape branch constructions — any
    // read yields SOME def's frozen field (init-before-use), so the
    // per-field hull encloses it.
    let func = branchy_pair(AggregateKind::Tuple, vec![fconst(3.0), fconst(4.0)]);
    assert_eq!(range_forbid(&func, None, &Operand::Copy(Place::field(3, 0))), Some((1.0, 3.0)));
    assert_eq!(range_forbid(&func, None, &Operand::Copy(Place::field(3, 1))), Some((2.0, 4.0)));
}

#[test]
fn multi_def_aggregate_shape_mismatch_fails_closed() {
    // Adversarial twins: positional Field(k) across differently-shaped
    // defs denotes differently-typed slots — every mismatch refuses.
    // (a) arity mismatch
    let func = branchy_pair(AggregateKind::Tuple, vec![fconst(3.0), fconst(4.0), fconst(5.0)]);
    assert_eq!(range_forbid(&func, None, &Operand::Copy(Place::field(3, 0))), None);
    // (b) kind mismatch (Tuple vs same-arity ADT)
    let adt = AggregateKind::Adt { name: "P".into(), variant: 0, active_field: None, args: None };
    let func = branchy_pair(adt, vec![fconst(3.0), fconst(4.0)]);
    assert_eq!(range_forbid(&func, None, &Operand::Copy(Place::field(3, 0))), None);
    // (c) variant mismatch without a Downcast read
    let v1 = AggregateKind::Adt {
        name: "core::option::Option".into(),
        variant: 1,
        active_field: None,
        args: None,
    };
    let func = branchy_pair(v1, vec![fconst(3.0), fconst(4.0)]);
    assert_eq!(range_forbid(&func, None, &Operand::Copy(Place::field(3, 0))), None);
}

#[test]
fn multi_def_aggregate_one_unbounded_element_fails_closed() {
    // One def's field is an uncontracted param — its slot poisons the
    // whole hull for that field.
    let func =
        branchy_pair(AggregateKind::Tuple, vec![Operand::Copy(Place::local(2)), fconst(4.0)]);
    assert_eq!(range_forbid(&func, None, &Operand::Copy(Place::field(3, 0))), None);
    // …and a contract on the param restores the hull.
    let mut bounded = func.clone();
    bounded.preconditions = both("x", 5.0);
    assert_eq!(
        range_forbid(&bounded, None, &Operand::Copy(Place::field(3, 0))),
        Some((-5.0, 5.0))
    );
}

// ---- W3 item 6: abs-guard caps (the fdiv probe) ----

/// The fdiv probe: `if b.abs() >= 1.0 && a.abs() <= <cap> { a / b }` —
/// non-strict Ge/Le forms, both guards threaded through abs temps.
/// `false_edge` routes the division through the cap guard's FALSE edge
/// (NaN-inclusive: must yield no bound); `reseat_a` writes the numerator
/// param in the body (defeats the cap's value identity).
fn fdiv_abs_probe(cap: f64, false_edge: bool, reseat_a: bool) -> VerifiableFunction {
    let mut bb3_stmts = vec![assign(
        Place::local(6),
        Rvalue::BinaryOp(BinOp::Le, Operand::Copy(Place::local(5)), fconst(cap)),
    )];
    if reseat_a {
        bb3_stmts.insert(0, assign(Place::local(1), Rvalue::Use(fconst(2.0))));
    }
    let (targets, otherwise) = if false_edge {
        (vec![(0u128, BlockId(4))], BlockId(5))
    } else {
        (vec![(0u128, BlockId(5))], BlockId(4))
    };
    make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("a")),
            decl(2, Ty::f64_ty(), Some("b")),
            decl(3, Ty::f64_ty(), None), // b.abs()
            decl(4, Ty::Bool, None),
            decl(5, Ty::f64_ty(), None), // a.abs()
            decl(6, Ty::Bool, None),
            decl(7, Ty::f64_ty(), None),
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "core::f64::<impl f64>::abs".to_string(),
                    args: vec![Operand::Copy(Place::local(2))],
                    dest: Place::local(3),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(
                    Place::local(4),
                    Rvalue::BinaryOp(BinOp::Ge, Operand::Copy(Place::local(3)), fconst(1.0)),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(4)),
                    targets: vec![(0, BlockId(5))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "core::f64::<impl f64>::abs".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(5),
                    target: Some(BlockId(3)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(3),
                stmts: bb3_stmts,
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(6)),
                    targets,
                    otherwise,
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![
                    assign(
                        Place::local(7),
                        Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    ),
                    assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(7)))),
                ],
                terminator: Terminator::Goto(BlockId(6)),
            },
            BasicBlock {
                id: BlockId(5),
                stmts: vec![assign(Place::local(0), Rvalue::Use(fconst(0.0)))],
                terminator: Terminator::Goto(BlockId(6)),
            },
            BasicBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
        Ty::f64_ty(),
        vec![],
    )
}

fn probe_div_discharges(func: &VerifiableFunction) -> bool {
    v2_float_binop_cannot_overflow_at(
        func,
        Some(BlockId(4)),
        None,
        BinOp::Div,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
    )
}

#[test]
fn abs_guard_cap_bounds_the_operand_and_discharges_the_probe_div() {
    // The fdiv probe (w3recon-2 class-b): `b.abs() >= 1.0 && a.abs() <=
    // 1e300` must discharge `a / b` — the cap gives `a ∈ [-1e300, 1e300]`
    // (non-strict Le threads through), the floor gives `|b| >= 1`, and
    // 1e300 / 1.0 sits under the 2^1020 margin. End-to-end through
    // `generate_v2_safety_vcs`: NO float obligation is minted.
    let func = fdiv_abs_probe(1.0e300, false, false);
    assert_eq!(
        range_forbid(&func, Some(BlockId(4)), &Operand::Copy(Place::local(1))),
        Some((-1.0e300, 1.0e300)),
        "the abs cap must materialize as a signed operand interval"
    );
    assert!(probe_div_discharges(&func));
    assert!(float_overflow_kinds(&func).is_empty(), "probe must be obligation-free");
}

#[test]
fn abs_guard_cap_false_edge_gives_no_bound() {
    // SOUNDNESS twin (NaN channel): on the FALSE edge the fact is
    // `¬(a.abs() <= cap)` — satisfied by NaN and by every huge numerator;
    // inverting it into any bound would be a false-proof channel.
    let func = fdiv_abs_probe(1.0e300, true, false);
    assert_eq!(range_forbid(&func, Some(BlockId(4)), &Operand::Copy(Place::local(1))), None);
    assert!(!probe_div_discharges(&func));
    assert!(!float_overflow_kinds(&func).is_empty());
}

#[test]
fn abs_guard_cap_on_reseated_operand_fails_closed() {
    // SOUNDNESS twin: the numerator param is written in the body — the
    // guarded abs magnitude is no longer the divided value.
    let func = fdiv_abs_probe(1.0e300, false, true);
    assert_eq!(range_forbid(&func, Some(BlockId(4)), &Operand::Copy(Place::local(1))), None);
    assert!(!probe_div_discharges(&func));
}

#[test]
fn abs_guard_negative_cap_is_refused() {
    // `a.abs() <= -1.0` can never be true — the dominated block is
    // unreachable; refuse rather than mint an empty-interval claim.
    let func = fdiv_abs_probe(-1.0, false, false);
    assert_eq!(range_forbid(&func, Some(BlockId(4)), &Operand::Copy(Place::local(1))), None);
    assert!(!probe_div_discharges(&func));
}

// ---- W3 item 7: contract magnitude hypotheses in the float VC ----

/// Count `BvULe(_, BitVec(bits(c) & mag_mask), 63)` hypothesis nodes.
fn bvule_threshold_count(f: &Formula, c: f64) -> usize {
    let want = (c.to_bits() & ((1u64 << 63) - 1)) as i128;
    let mut n = 0;
    f.visit(&mut |sub| {
        if let Formula::BvULe(_, rhs, 63) = sub
            && let Formula::BitVec { value, width: 63 } = rhs.as_ref()
            && *value == want
        {
            n += 1;
        }
    });
    n
}

fn has_any_bvule(f: &Formula) -> bool {
    let mut found = false;
    f.visit(&mut |sub| {
        if matches!(sub, Formula::BvULe(..)) {
            found = true;
        }
    });
    found
}

fn float_overflow_formulas(func: &VerifiableFunction) -> Vec<Formula> {
    generate_v2_safety_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { .. }))
        .map(|vc| vc.formula)
        .collect()
}

#[test]
fn contract_magnitude_hypothesis_is_conjoined_into_the_float_vc() {
    // |a| <= 1e300 (too big for the tiny-addend discharge), b unbounded:
    // the Sub obligation is minted AND carries the pure-BV hypothesis
    // `mag(a) <= bits(1e300)` for the solver lane.
    let mut func = sub_func(false);
    func.preconditions = both("a", 1e300);
    let formulas = float_overflow_formulas(&func);
    assert_eq!(formulas.len(), 1, "the Sub VC must be minted: {formulas:?}");
    assert_eq!(
        bvule_threshold_count(&formulas[0], 1e300),
        1,
        "exactly one hypothesis for the contracted operand: {:?}",
        formulas[0]
    );
}

#[test]
fn contract_hypotheses_cover_both_contracted_operands() {
    // Near-MAX bounds keep the obligation (non-finite interval endpoints)
    // — the VC then carries one hypothesis per operand, each at its own
    // contract threshold.
    let mut func = sub_func(false);
    let mut pre = both("a", f64::MAX);
    pre.extend(both("b", 1e308));
    func.preconditions = pre;
    let formulas = float_overflow_formulas(&func);
    assert_eq!(formulas.len(), 1, "{formulas:?}");
    assert_eq!(bvule_threshold_count(&formulas[0], f64::MAX), 1);
    assert_eq!(bvule_threshold_count(&formulas[0], 1e308), 1);
}

#[test]
fn no_hypothesis_without_an_entry_stable_two_sided_contract() {
    // (a) uncontracted operands: no BvULe node anywhere in the witness.
    let formulas = float_overflow_formulas(&sub_func(false));
    assert_eq!(formulas.len(), 1);
    assert!(!has_any_bvule(&formulas[0]), "uncontracted: {:?}", formulas[0]);
    // (b) SOUNDNESS twin — entry-UNSTABLE operand: the body writes `a`,
    // so the contract speaks about a value the op may not read; the
    // hypothesis must NOT be emitted.
    let mut unstable = sub_func(false);
    unstable.preconditions = both("a", 1e300);
    unstable.body.blocks[0].stmts.push(assign(Place::local(1), Rvalue::Use(fconst(1.0))));
    let formulas = float_overflow_formulas(&unstable);
    assert_eq!(formulas.len(), 1);
    assert!(!has_any_bvule(&formulas[0]), "entry-unstable: {:?}", formulas[0]);
    // (c) one-sided bound: contract_range's two-sided discipline refuses.
    let mut one_sided = sub_func(false);
    one_sided.preconditions = vec![Formula::And(vec![le_f("a", 1e300)])];
    let formulas = float_overflow_formulas(&one_sided);
    assert_eq!(formulas.len(), 1);
    assert!(!has_any_bvule(&formulas[0]), "one-sided: {:?}", formulas[0]);
}

#[test]
fn hypothesis_encoding_matches_the_witness_magnitude_grammar() {
    // Unit shape check: BvULe over the SAME magnitude extract the witness
    // uses (low 63 bits), against the bound's sign-stripped bit pattern.
    // A repeated operand place is emitted once.
    let mut func = sub_func(false);
    func.preconditions = both("a", 1e300);
    let a = Operand::Copy(Place::local(1));
    let hyps = v2_float_contract_magnitude_hypotheses(&func, &a, &a);
    assert_eq!(hyps.len(), 1, "same place twice must dedupe: {hyps:?}");
    let Formula::BvULe(lhs, rhs, 63) = &hyps[0] else {
        panic!("expected BvULe at magnitude width, got {:?}", hyps[0]);
    };
    assert!(
        matches!(lhs.as_ref(), Formula::BvExtract { high: 62, low: 0, .. }),
        "lhs must be the witness magnitude extract: {lhs:?}"
    );
    assert!(
        matches!(rhs.as_ref(), Formula::BitVec { value, width: 63 }
            if *value == ((1e300f64.to_bits() & ((1u64 << 63) - 1)) as i128)),
        "rhs must be the sign-stripped bound bits: {rhs:?}"
    );
}

#[test]
fn temp_copy_of_contracted_param_resolves_to_the_contract_bound() {
    // Real-MIR shape (the a3d Quat/Vec chains): the binop reads a compiler
    // TEMP holding a stable copy of the contracted param (`_3 = a;
    // _0 = _3 - b`) — the def-chain resolution must find `a`'s two-sided
    // contract THROUGH the temp and mint the hypothesis on the temp's own
    // term.
    let mut func = make(
        vec![
            decl(0, Ty::f64_ty(), None),
            decl(1, Ty::f64_ty(), Some("a")),
            decl(2, Ty::f64_ty(), Some("b")),
            decl(3, Ty::f64_ty(), None),
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(
                    Place::local(0),
                    Rvalue::BinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(3)),
                        Operand::Copy(Place::local(2)),
                    ),
                ),
            ],
            terminator: Terminator::Return,
        }],
        2,
        Ty::f64_ty(),
        both("a", 1e300),
    );
    let formulas = float_overflow_formulas(&func);
    assert_eq!(formulas.len(), 1, "{formulas:?}");
    assert_eq!(
        bvule_threshold_count(&formulas[0], 1e300),
        1,
        "temp-resolved hypothesis: {:?}",
        formulas[0]
    );

    // SOUNDNESS twin: a SECOND def of the temp breaks single-def stability
    // — the temp may not hold the contracted entry value at the op; the
    // resolution must refuse.
    func.body.blocks[0].stmts.insert(1, assign(Place::local(3), Rvalue::Use(fconst(1.0))));
    let formulas = float_overflow_formulas(&func);
    assert_eq!(formulas.len(), 1);
    assert!(!has_any_bvule(&formulas[0]), "multi-def temp must refuse: {:?}", formulas[0]);
}
