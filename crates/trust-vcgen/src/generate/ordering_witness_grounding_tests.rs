//! Ordering/sign-witness return grounding (b62 F4): the gate
//! (`ordering_witness_credited_items`) and the pin loop must agree, the
//! emitted ordering fact must bind the DOMINATING GUARD's bool edge
//! (never a re-encoding of the opaque handle ints), and every
//! unresolvable shape must stay at the fail-closed SpecModelUngrounded
//! Unknown. Fixtures mirror the `-Ztrust-dump=mir:<dir>` ground truth of the
//! reshaped ny-cert wrappers (selfcheck::check_entailment /
//! check_farkas, branch::check_branch_tree) and the ORIGINAL
//! check_farkas `Not(is_positive)` / `is_negative` two-def join.

use trust_types::{
    AggregateKind, BasicBlock, BlockId, ConstValue, Contract, ContractKind, Formula,
    LocalDecl, Operand, Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator,
    Ty, UnOp, VariantDef, VcKind, VerifiableBody, VerifiableFunction,
};

use super::{generate_v2_contract_vcs_impl, parse_ok_pair_model_var, parse_sign_model_var};

const OK0: &str = "_0_value.__trust_ok_0";
const OK1: &str = "_0_value.__trust_ok_1";
const SIGN: &str = "_0_value_sign";

fn i64_ty() -> Ty {
    Ty::Int { width: 64, signed: true }
}

fn rat_ty() -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        name: "rational::Rat".into(),
        fields: vec![("id".into(), Ty::Int { width: 32, signed: false })],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

fn pair_ty() -> Ty {
    Ty::Tuple(vec![rat_ty(), rat_ty()])
}

fn ref_rat_ty() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(rat_ty()) }
}

/// `std::result::Result<ok_payload, i64>` in the flattened lowering shape
/// (machine tags: Ok = 0, Err = 1).
fn result_ty(ok_payload: Ty) -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        name: "std::result::Result".into(),
        fields: vec![
            ("__tag".into(), i64_ty()),
            ("__v0_0".into(), ok_payload.clone()),
            ("__v1_0".into(), i64_ty()),
        ],
        variants: vec![
            VariantDef { name: "Ok".into(), discriminant: 0, fields: vec![("0".into(), ok_payload)] },
            VariantDef { name: "Err".into(), discriminant: 1, fields: vec![("0".into(), i64_ty())] },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

fn func_with(
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
    ret_ty: Ty,
    ensures: &str,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "ord_pair".to_string(),
        def_path: "test::ord_pair".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count, return_ty: ret_ty },
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: ensures.to_string(),
        }],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn call(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: Default::default(),
    }
}

fn switch(discr: Operand, targets: Vec<(u128, usize)>, otherwise: usize) -> Terminator {
    Terminator::SwitchInt {
        discr,
        targets: targets.into_iter().map(|(v, t)| (v, BlockId(t))).collect(),
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

fn downcast_field(local: usize, variant: usize) -> Place {
    Place {
        local,
        projections: vec![Projection::Downcast(variant), Projection::Field(0)],
    }
}

fn field(local: usize, i: usize) -> Place {
    Place { local, projections: vec![Projection::Field(i)] }
}

fn ok_aggregate(op: Operand) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt { name: "std::result::Result".into(), variant: 0, active_field: None, args: None },
        vec![op],
    )
}

fn err_aggregate(op: Operand) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt { name: "std::result::Result".into(), variant: 1, active_field: None, args: None },
        vec![op],
    )
}

/// True iff SOME subformula satisfies `pred`. A multi-arm fixture's
/// obligation is duplicated per guard path by the v2 per-path machinery,
/// so the pins are asserted by SHAPE anywhere in the tree — every
/// asserted pin shape (`Le`/`Ge`/`Not(Eq)` over the model vars,
/// `_0_discr == 1`) is one the negated postcondition itself cannot
/// contain, so a match can only be a lane-emitted pin.
fn subformula_has(formula: &Formula, pred: &dyn Fn(&Formula) -> bool) -> bool {
    let mut found = false;
    formula.visit(&mut |f| {
        if pred(f) {
            found = true;
        }
    });
    found
}

fn var_is(f: &Formula, name: &str) -> bool {
    matches!(f, Formula::Var(n, _) if n == name)
}

/// The lane's parser-convention Ok pin `_0_discr == 1` — an atom only the
/// pin loop mints (the lowered `is_ok` postcondition atoms compare to 0).
fn has_ok_discr_pin(f: &Formula) -> bool {
    subformula_has(f, &|f| {
        matches!(f, Formula::Eq(l, r)
            if var_is(l, "_0_discr") && matches!(&**r, Formula::Int(1)))
    })
}

fn postcondition_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect()
}

fn ungrounded_details(func: &VerifiableFunction) -> Vec<String> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter_map(|vc| match vc.kind {
            VcKind::UnsupportedMir { kind, detail, .. }
                if kind == crate::contracts::SPEC_MODEL_UNGROUNDED_KIND =>
            {
                Some(detail)
            }
            _ => None,
        })
        .collect()
}

fn ok_path_vc(
    vcs: &[trust_types::VerificationCondition],
) -> &trust_types::VerificationCondition {
    vcs.iter()
        .find(|vc| has_ok_discr_pin(&vc.formula))
        .unwrap_or_else(|| panic!("the Ok path VC pins _0_discr == 1: {vcs:#?}"))
}

const GT_PAIR_ENSURES: &str = "!((result.is_ok()) && \
     ((result.unwrap().__trust_ok_0) > (result.unwrap().__trust_ok_1)))";
const LT_PAIR_ENSURES: &str = "!((result.is_ok()) && \
     ((result.unwrap().__trust_ok_0) < (result.unwrap().__trust_ok_1)))";
const EQ_PAIR_ENSURES: &str = "!((result.is_ok()) && \
     ((result.unwrap().__trust_ok_0) == (result.unwrap().__trust_ok_1)))";
const SIGN_ENSURES: &str = "!((result.is_ok()) && (result.unwrap().is_positive()))";

/// The reshaped `check_entailment`/`check_chain` wrapper (real
/// `-Ztrust-dump=mir:<dir>` shape): extract the pair from an opaque inner call,
/// guard with the pair's OWN `PartialOrd` comparison (`cmp_method`,
/// Err on the TRUE edge), return `Ok((d, c))` on the false edge.
/// `guarded = false` drops the guard entirely (the fail-closed negative);
/// `mutate_after_guard` rewrites `d` between the guard and the tuple.
fn pair_wrapper_fn(
    cmp_method: &str,
    guarded: bool,
    mutate_after_guard: bool,
    ensures: &str,
) -> VerifiableFunction {
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(pair_ty()), name: None },
        LocalDecl { index: 1, ty: i64_ty(), name: None }, // param
        LocalDecl { index: 2, ty: i64_ty(), name: None },
        LocalDecl { index: 3, ty: result_ty(pair_ty()), name: None }, // Ok temp
        LocalDecl { index: 4, ty: rat_ty(), name: None },             // d
        LocalDecl { index: 5, ty: rat_ty(), name: None },             // c
        LocalDecl { index: 6, ty: result_ty(pair_ty()), name: None }, // inner dest
        LocalDecl { index: 7, ty: i64_ty(), name: None },             // discr temp
        LocalDecl { index: 8, ty: pair_ty(), name: None },            // extracted pair
        LocalDecl { index: 9, ty: i64_ty(), name: None },             // Err payload
        LocalDecl { index: 10, ty: result_ty(pair_ty()), name: None }, // Err temp
        LocalDecl { index: 11, ty: Ty::Bool, name: None },            // guard dest
        LocalDecl { index: 12, ty: ref_rat_ty(), name: None },
        LocalDecl { index: 13, ty: ref_rat_ty(), name: None },
        LocalDecl { index: 14, ty: result_ty(pair_ty()), name: None }, // guard-Err temp
        LocalDecl { index: 16, ty: pair_ty(), name: None },           // tuple temp
    ];
    let cmp_callee = format!("<rational::Rat as std::cmp::PartialOrd>::{cmp_method}");
    let mut ok_stmts = Vec::new();
    if mutate_after_guard {
        // A second write into `d` AFTER the guard compared it: the
        // returned pair no longer carries the compared value.
        ok_stmts.push(assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(5)))));
    }
    ok_stmts.extend([
        assign(
            Place::local(16),
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![Operand::Copy(Place::local(4)), Operand::Copy(Place::local(5))],
            ),
        ),
        assign(Place::local(3), ok_aggregate(Operand::Move(Place::local(16)))),
        assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(3)))),
    ]);
    let ret = if guarded { 8 } else { 5 };
    let mut blocks = vec![
        BasicBlock { id: BlockId(0), stmts: vec![], terminator: call("test::inner", vec![], 6, 1) },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(7), Rvalue::Discriminant(Place::local(6)))],
            terminator: switch(Operand::Move(Place::local(7)), vec![(0, 4), (1, 3)], 2),
        },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Unreachable },
        // extract-Err path: `Err(e) => return Err(e)`.
        BasicBlock {
            id: BlockId(3),
            stmts: vec![
                assign(Place::local(9), Rvalue::Use(Operand::Move(downcast_field(6, 1)))),
                assign(Place::local(10), err_aggregate(Operand::Copy(Place::local(9)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(10)))),
            ],
            terminator: Terminator::Goto(BlockId(ret)),
        },
    ];
    if guarded {
        blocks.extend([
            // Ok extract + the pair's own comparison.
            BasicBlock {
                id: BlockId(4),
                stmts: vec![
                    assign(Place::local(8), Rvalue::Use(Operand::Copy(downcast_field(6, 0)))),
                    assign(Place::local(4), Rvalue::Use(Operand::Copy(field(8, 0)))),
                    assign(Place::local(5), Rvalue::Use(Operand::Copy(field(8, 1)))),
                    assign(Place::local(12), Rvalue::Ref { mutable: false, place: Place::local(4) }),
                    assign(Place::local(13), Rvalue::Ref { mutable: false, place: Place::local(5) }),
                ],
                terminator: call(
                    &cmp_callee,
                    vec![Operand::Move(Place::local(12)), Operand::Move(Place::local(13))],
                    11,
                    5,
                ),
            },
            BasicBlock {
                id: BlockId(5),
                stmts: vec![],
                terminator: switch(Operand::Move(Place::local(11)), vec![(0, 7)], 6),
            },
            // guard-Err path.
            BasicBlock {
                id: BlockId(6),
                stmts: vec![
                    assign(Place::local(14), err_aggregate(Operand::Constant(ConstValue::Int(1)))),
                    assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(14)))),
                ],
                terminator: Terminator::Goto(BlockId(8)),
            },
            // Ok path.
            BasicBlock { id: BlockId(7), stmts: ok_stmts, terminator: Terminator::Goto(BlockId(8)) },
            BasicBlock { id: BlockId(8), stmts: vec![], terminator: Terminator::Return },
        ]);
    } else {
        let mut stmts = vec![
            assign(Place::local(8), Rvalue::Use(Operand::Copy(downcast_field(6, 0)))),
            assign(Place::local(4), Rvalue::Use(Operand::Copy(field(8, 0)))),
            assign(Place::local(5), Rvalue::Use(Operand::Copy(field(8, 1)))),
        ];
        stmts.extend(ok_stmts);
        blocks.extend([
            BasicBlock { id: BlockId(4), stmts, terminator: Terminator::Goto(BlockId(5)) },
            BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
        ]);
    }
    func_with(locals, blocks, 1, result_ty(pair_ty()), ensures)
}

/// The reshaped `check_branch_tree` wrapper (real `-Ztrust-dump=mir:<dir>`
/// shape): the guard bool has TWO call-dest defs — `lt(&g, &t)` on one
/// direction arm, `gt(&g, &t)` on the other — and the Ok tuple sits on
/// the guard's TRUE edge (`if !cleared { return Err }` compiles to the
/// inverted switch). The joined true-edge fact is {Lt} ∪ {Gt} = ¬Eq.
fn direction_pair_wrapper_fn() -> VerifiableFunction {
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(pair_ty()), name: None },
        LocalDecl { index: 1, ty: i64_ty(), name: None }, // direction param
        LocalDecl { index: 2, ty: i64_ty(), name: None },
        LocalDecl { index: 3, ty: result_ty(pair_ty()), name: None },
        LocalDecl { index: 4, ty: rat_ty(), name: None }, // g
        LocalDecl { index: 5, ty: rat_ty(), name: None }, // t
        LocalDecl { index: 6, ty: result_ty(pair_ty()), name: None },
        LocalDecl { index: 7, ty: i64_ty(), name: None },
        LocalDecl { index: 8, ty: pair_ty(), name: None },
        LocalDecl { index: 9, ty: i64_ty(), name: None },
        LocalDecl { index: 10, ty: result_ty(pair_ty()), name: None },
        LocalDecl { index: 11, ty: Ty::Bool, name: None }, // cleared (2 defs)
        LocalDecl { index: 12, ty: ref_rat_ty(), name: None },
        LocalDecl { index: 13, ty: ref_rat_ty(), name: None },
        LocalDecl { index: 14, ty: ref_rat_ty(), name: None },
        LocalDecl { index: 15, ty: ref_rat_ty(), name: None },
        LocalDecl { index: 16, ty: pair_ty(), name: None },
        LocalDecl { index: 17, ty: Ty::Bool, name: None }, // switch copy
        LocalDecl { index: 18, ty: result_ty(pair_ty()), name: None },
    ];
    let blocks = vec![
        BasicBlock { id: BlockId(0), stmts: vec![], terminator: call("test::inner", vec![], 6, 1) },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(7), Rvalue::Discriminant(Place::local(6)))],
            terminator: switch(Operand::Move(Place::local(7)), vec![(0, 4), (1, 3)], 2),
        },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Unreachable },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![
                assign(Place::local(9), Rvalue::Use(Operand::Move(downcast_field(6, 1)))),
                assign(Place::local(10), err_aggregate(Operand::Copy(Place::local(9)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(10)))),
            ],
            terminator: Terminator::Goto(BlockId(10)),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![
                assign(Place::local(8), Rvalue::Use(Operand::Copy(downcast_field(6, 0)))),
                assign(Place::local(4), Rvalue::Use(Operand::Copy(field(8, 0)))),
                assign(Place::local(5), Rvalue::Use(Operand::Copy(field(8, 1)))),
            ],
            terminator: switch(Operand::Copy(Place::local(1)), vec![(0, 6)], 5),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: vec![
                assign(Place::local(12), Rvalue::Ref { mutable: false, place: Place::local(4) }),
                assign(Place::local(13), Rvalue::Ref { mutable: false, place: Place::local(5) }),
            ],
            terminator: call(
                "<rational::Rat as std::cmp::PartialOrd>::lt",
                vec![Operand::Move(Place::local(12)), Operand::Move(Place::local(13))],
                11,
                7,
            ),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![
                assign(Place::local(14), Rvalue::Ref { mutable: false, place: Place::local(4) }),
                assign(Place::local(15), Rvalue::Ref { mutable: false, place: Place::local(5) }),
            ],
            terminator: call(
                "<rational::Rat as std::cmp::PartialOrd>::gt",
                vec![Operand::Move(Place::local(14)), Operand::Move(Place::local(15))],
                11,
                7,
            ),
        },
        BasicBlock {
            id: BlockId(7),
            stmts: vec![assign(Place::local(17), Rvalue::Use(Operand::Copy(Place::local(11))))],
            terminator: switch(Operand::Move(Place::local(17)), vec![(0, 8)], 9),
        },
        BasicBlock {
            id: BlockId(8),
            stmts: vec![
                assign(Place::local(18), err_aggregate(Operand::Constant(ConstValue::Int(1)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(18)))),
            ],
            terminator: Terminator::Goto(BlockId(10)),
        },
        BasicBlock {
            id: BlockId(9),
            stmts: vec![
                assign(
                    Place::local(16),
                    Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![Operand::Copy(Place::local(4)), Operand::Copy(Place::local(5))],
                    ),
                ),
                assign(Place::local(3), ok_aggregate(Operand::Move(Place::local(16)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(3)))),
            ],
            terminator: Terminator::Goto(BlockId(10)),
        },
        BasicBlock { id: BlockId(10), stmts: vec![], terminator: Terminator::Return },
    ];
    func_with(locals, blocks, 1, result_ty(pair_ty()), EQ_PAIR_ENSURES)
}

/// The reshaped `check_farkas` wrapper (real `-Ztrust-dump=mir:<dir>` shape):
/// single `is_positive` def on the extracted payload (by-VALUE Copy
/// operand), Ok on the guard's FALSE edge.
fn sign_wrapper_fn() -> VerifiableFunction {
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(rat_ty()), name: None },
        LocalDecl { index: 1, ty: i64_ty(), name: None },
        LocalDecl { index: 2, ty: i64_ty(), name: None },
        LocalDecl { index: 3, ty: result_ty(rat_ty()), name: None },
        LocalDecl { index: 4, ty: result_ty(rat_ty()), name: None }, // inner dest
        LocalDecl { index: 5, ty: i64_ty(), name: None },
        LocalDecl { index: 6, ty: rat_ty(), name: None }, // c
        LocalDecl { index: 7, ty: i64_ty(), name: None },
        LocalDecl { index: 8, ty: result_ty(rat_ty()), name: None },
        LocalDecl { index: 9, ty: Ty::Bool, name: None },
        LocalDecl { index: 10, ty: result_ty(rat_ty()), name: None },
    ];
    let blocks = vec![
        BasicBlock { id: BlockId(0), stmts: vec![], terminator: call("test::inner", vec![], 4, 1) },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(5), Rvalue::Discriminant(Place::local(4)))],
            terminator: switch(Operand::Move(Place::local(5)), vec![(0, 4), (1, 3)], 2),
        },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Unreachable },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![
                assign(Place::local(7), Rvalue::Use(Operand::Move(downcast_field(4, 1)))),
                assign(Place::local(8), err_aggregate(Operand::Copy(Place::local(7)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(8)))),
            ],
            terminator: Terminator::Goto(BlockId(8)),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![assign(Place::local(6), Rvalue::Use(Operand::Copy(downcast_field(4, 0))))],
            terminator: call(
                "rational::Rat::is_positive",
                vec![Operand::Copy(Place::local(6))],
                9,
                5,
            ),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: vec![],
            terminator: switch(Operand::Move(Place::local(9)), vec![(0, 7)], 6),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![
                assign(Place::local(10), err_aggregate(Operand::Constant(ConstValue::Int(1)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(10)))),
            ],
            terminator: Terminator::Goto(BlockId(8)),
        },
        BasicBlock {
            id: BlockId(7),
            stmts: vec![
                assign(Place::local(3), ok_aggregate(Operand::Copy(Place::local(6)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(3)))),
            ],
            terminator: Terminator::Goto(BlockId(8)),
        },
        BasicBlock { id: BlockId(8), stmts: vec![], terminator: Terminator::Return },
    ];
    func_with(locals, blocks, 1, result_ty(rat_ty()), SIGN_ENSURES)
}

/// The ORIGINAL (pre-reshape) `check_farkas` contradiction shape: the
/// guard bool has TWO defs — a statement `Not(<is_positive dest>)` on the
/// strict arm and the `is_negative` CALL dest on the non-strict arm — and
/// Ok sits on the TRUE edge. Per-def true-edge facts {Le} ∪ {Lt} = Le.
fn sign_not_hop_fn() -> VerifiableFunction {
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(rat_ty()), name: None },
        LocalDecl { index: 1, ty: i64_ty(), name: None }, // strictness param
        LocalDecl { index: 2, ty: rat_ty(), name: None }, // c
        LocalDecl { index: 3, ty: result_ty(rat_ty()), name: None },
        LocalDecl { index: 4, ty: result_ty(rat_ty()), name: None }, // inner dest
        LocalDecl { index: 5, ty: i64_ty(), name: None },
        LocalDecl { index: 6, ty: i64_ty(), name: None },
        LocalDecl { index: 7, ty: result_ty(rat_ty()), name: None },
        LocalDecl { index: 8, ty: Ty::Bool, name: None },  // is_positive dest
        LocalDecl { index: 9, ty: Ty::Bool, name: None },  // contradiction (2 defs)
        LocalDecl { index: 10, ty: Ty::Bool, name: None }, // switch copy
        LocalDecl { index: 11, ty: result_ty(rat_ty()), name: None },
    ];
    let blocks = vec![
        BasicBlock { id: BlockId(0), stmts: vec![], terminator: call("test::inner", vec![], 4, 1) },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(5), Rvalue::Discriminant(Place::local(4)))],
            terminator: switch(Operand::Move(Place::local(5)), vec![(0, 3), (1, 2)], 9),
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![
                assign(Place::local(6), Rvalue::Use(Operand::Move(downcast_field(4, 1)))),
                assign(Place::local(7), err_aggregate(Operand::Copy(Place::local(6)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(7)))),
            ],
            terminator: Terminator::Goto(BlockId(10)),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![assign(Place::local(2), Rvalue::Use(Operand::Copy(downcast_field(4, 0))))],
            terminator: switch(Operand::Copy(Place::local(1)), vec![(0, 5)], 4),
        },
        // strict arm: `!c.is_positive()`.
        BasicBlock {
            id: BlockId(4),
            stmts: vec![],
            terminator: call(
                "rational::Rat::is_positive",
                vec![Operand::Copy(Place::local(2))],
                8,
                6,
            ),
        },
        // non-strict arm: `c.is_negative()` — dest IS the guard bool.
        BasicBlock {
            id: BlockId(5),
            stmts: vec![],
            terminator: call(
                "rational::Rat::is_negative",
                vec![Operand::Copy(Place::local(2))],
                9,
                7,
            ),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![assign(
                Place::local(9),
                Rvalue::UnaryOp(UnOp::Not, Operand::Move(Place::local(8))),
            )],
            terminator: Terminator::Goto(BlockId(7)),
        },
        BasicBlock {
            id: BlockId(7),
            stmts: vec![assign(Place::local(10), Rvalue::Use(Operand::Copy(Place::local(9))))],
            terminator: switch(Operand::Move(Place::local(10)), vec![(0, 8)], 11),
        },
        BasicBlock {
            id: BlockId(8),
            stmts: vec![
                assign(Place::local(11), err_aggregate(Operand::Constant(ConstValue::Int(1)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(11)))),
            ],
            terminator: Terminator::Goto(BlockId(10)),
        },
        BasicBlock { id: BlockId(9), stmts: vec![], terminator: Terminator::Unreachable },
        BasicBlock { id: BlockId(10), stmts: vec![], terminator: Terminator::Return },
        BasicBlock {
            id: BlockId(11),
            stmts: vec![
                assign(Place::local(3), ok_aggregate(Operand::Copy(Place::local(2)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(3)))),
            ],
            terminator: Terminator::Goto(BlockId(10)),
        },
    ];
    func_with(locals, blocks, 1, result_ty(rat_ty()), SIGN_ENSURES)
}

#[test]
fn ok_pair_and_sign_model_var_parsers_are_strict() {
    let v = parse_ok_pair_model_var(OK0).expect("tuple-bind shape parses");
    assert_eq!((v.name.as_str(), v.index), (OK0, 0));
    // Versioned copies parse to the BASE name.
    assert_eq!(
        parse_ok_pair_model_var("_0_value.__trust_ok_1#s1_0").map(|v| v.index),
        Some(1)
    );
    // Trailing projections, non-numeric indices, other bases: fail closed.
    assert!(parse_ok_pair_model_var("_0_value.__trust_ok_0.1").is_none());
    assert!(parse_ok_pair_model_var("_0_value.__trust_ok_").is_none());
    assert!(parse_ok_pair_model_var("_0_value.0").is_none());
    assert!(parse_ok_pair_model_var("x.__trust_ok_0").is_none());
    assert_eq!(parse_sign_model_var("_0_value_sign").as_deref(), Some(SIGN));
    assert_eq!(parse_sign_model_var("_0_value_sign#s2_1").as_deref(), Some(SIGN));
    assert!(parse_sign_model_var("c_sign").is_none());
    assert!(parse_sign_model_var("_0_value_sign.0").is_none());
    assert!(parse_sign_model_var("_0_value").is_none());
}

#[test]
fn guarded_pair_wrapper_grounds_ordering_atom_on_guard_bool() {
    // The reshaped check_entailment/check_chain shape: `gt(&d, &c)` with
    // Err on the true edge, so the Ok edge admits {Lt, Eq} — the pin is
    // `ok_0 <= ok_1`, which contradicts the negated `!(… if d > c)`
    // obligation (`Gt`). All three return paths yield VCs; the Err paths
    // pin only the discr. No ungrounded row remains.
    let func = pair_wrapper_fn("gt", true, false, GT_PAIR_ENSURES);
    assert!(ungrounded_details(&func).is_empty(), "pair must be credited");
    let vcs = postcondition_vcs(&func);
    assert_eq!(vcs.len(), 3, "extract-Err + guard-Err + Ok paths: {vcs:#?}");
    let ok_vc = ok_path_vc(&vcs);
    assert!(
        subformula_has(&ok_vc.formula, &|f| matches!(f, Formula::Le(l, r)
            if var_is(l, OK0) && var_is(r, OK1))),
        "Ok path must pin the guard's false-edge fact ok_0 <= ok_1: {:#?}",
        ok_vc.formula
    );
    assert_eq!(
        vcs.iter().filter(|vc| has_ok_discr_pin(&vc.formula)).count(),
        1,
        "exactly the Ok path pins _0_discr == 1 (the Err paths pin 0): {vcs:#?}"
    );
    // The Le pin must ride ONLY the Ok path: an Err path carries no
    // ordering fact (the payload terms have no denotation there).
    for vc in &vcs {
        if !has_ok_discr_pin(&vc.formula) {
            assert!(
                !subformula_has(&vc.formula, &|f| matches!(f, Formula::Le(l, r)
                    if var_is(l, OK0) && var_is(r, OK1))),
                "Err paths must not carry the ordering pin: {:#?}",
                vc.formula
            );
        }
    }
}

#[test]
fn opposite_polarity_guard_grounds_ge_fact() {
    // Same wrapper, opposite comparison: `lt(&d, &c)` guarding a
    // `!(… if d < c)` ensures. The Ok edge (false) admits {Gt, Eq} — the
    // pin is `ok_0 >= ok_1`.
    let func = pair_wrapper_fn("lt", true, false, LT_PAIR_ENSURES);
    assert!(ungrounded_details(&func).is_empty(), "pair must be credited");
    let vcs = postcondition_vcs(&func);
    let ok_vc = ok_path_vc(&vcs);
    assert!(
        subformula_has(&ok_vc.formula, &|f| matches!(f, Formula::Ge(l, r)
            if var_is(l, OK0) && var_is(r, OK1))),
        "Ok path must pin ok_0 >= ok_1: {:#?}",
        ok_vc.formula
    );
}

#[test]
fn two_def_direction_guard_grounds_disequality() {
    // The reshaped check_branch_tree shape: the guard bool is defined by
    // BOTH `lt(&g, &t)` and `gt(&g, &t)` (one per direction arm) and Ok
    // sits on the TRUE edge — the per-def join {Lt} ∪ {Gt} pins
    // `!(ok_0 == ok_1)`, which contradicts the negated `!(… if g == t)`
    // obligation.
    let func = direction_pair_wrapper_fn();
    assert!(ungrounded_details(&func).is_empty(), "pair must be credited");
    let vcs = postcondition_vcs(&func);
    let ok_vc = ok_path_vc(&vcs);
    assert!(
        subformula_has(&ok_vc.formula, &|f| matches!(f, Formula::Not(inner)
            if matches!(&**inner, Formula::Eq(l, r) if var_is(l, OK0) && var_is(r, OK1)))),
        "Ok path must pin !(ok_0 == ok_1): {:#?}",
        ok_vc.formula
    );
}

#[test]
fn sign_guard_grounds_sign_atom_on_guard_bool() {
    // The reshaped check_farkas shape: `is_positive(c)` with Err on the
    // true edge — the Ok edge admits {Lt, Eq}, pinned `sign <= 0`, which
    // contradicts the negated `!(… if c.is_positive())` obligation
    // (`sign > 0`).
    let func = sign_wrapper_fn();
    assert!(ungrounded_details(&func).is_empty(), "sign term must be credited");
    let vcs = postcondition_vcs(&func);
    assert_eq!(vcs.len(), 3, "extract-Err + guard-Err + Ok paths: {vcs:#?}");
    let ok_vc = ok_path_vc(&vcs);
    assert!(
        subformula_has(&ok_vc.formula, &|f| matches!(f, Formula::Le(l, r)
            if var_is(l, SIGN) && matches!(&**r, Formula::Int(0)))),
        "Ok path must pin sign <= 0: {:#?}",
        ok_vc.formula
    );
}

#[test]
fn not_hop_and_is_negative_defs_join_to_le() {
    // The ORIGINAL check_farkas contradiction bool: one def is
    // `Not(is_positive(c))` (statement Not over a call dest), the other
    // the `is_negative(c)` call dest; Ok on the TRUE edge. Per-def
    // true-edge facts complement({Gt}) = {Lt, Eq} and {Lt} join to
    // {Lt, Eq} — pinned `sign <= 0`.
    let func = sign_not_hop_fn();
    assert!(ungrounded_details(&func).is_empty(), "sign term must be credited");
    let vcs = postcondition_vcs(&func);
    let ok_vc = ok_path_vc(&vcs);
    assert!(
        subformula_has(&ok_vc.formula, &|f| matches!(f, Formula::Le(l, r)
            if var_is(l, SIGN) && matches!(&**r, Formula::Int(0)))),
        "Ok path must pin sign <= 0: {:#?}",
        ok_vc.formula
    );
}

#[test]
fn unguarded_comparison_stays_fail_closed() {
    // SOUNDNESS PIN: no dominating comparison guard — the returned pair
    // may genuinely violate the ordering, so nothing may be pinned. The
    // pair stays uncredited: no refutable Postcondition VC, one
    // SpecModelUngrounded row naming both pair terms (and not the
    // groundable `_0_discr`).
    let func = pair_wrapper_fn("gt", false, false, GT_PAIR_ENSURES);
    assert!(
        postcondition_vcs(&func).is_empty(),
        "an unguarded pair must not emit a refutable Postcondition VC"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(
        details[0].contains(OK0) && details[0].contains(OK1) && !details[0].contains("_0_discr"),
        "both pair terms fail closed: {}",
        details[0]
    );
}

#[test]
fn mutation_after_guard_stays_fail_closed() {
    // SOUNDNESS PIN (temporal validity): the guard compared `d`, but `d`
    // is rewritten AFTER the guard and BEFORE the tuple — the returned
    // pair no longer carries the compared value.
    // `place_source_is_stable(d)` fails on the second def, the candidate
    // unfold stops above it, no witness operand matches, and the pair
    // stays uncredited: no refutable VC, one ungrounded row.
    let func = pair_wrapper_fn("gt", true, true, GT_PAIR_ENSURES);
    assert!(
        postcondition_vcs(&func).is_empty(),
        "a mutated component must not reach the refutable lane"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(details[0].contains(OK0) && details[0].contains(OK1), "{}", details[0]);
}

#[test]
fn discreteness_shaped_contracts_stay_fail_closed() {
    // SOUNDNESS PIN (no Int-discreteness import): atoms that relate a
    // credited term to anything but its partner var / the literal 0 —
    // `ok_0 >= ok_1 + 1` (arithmetic), `sign > 1` (nonzero constant) —
    // are exactly the shapes whose Int reading could smuggle in
    // discreteness (`x > 0 ⟹ x >= 1`). The coverage gates refuse them:
    // fail-closed Unknown, never a (dis)provable VC.
    let discr_ok = Formula::Not(Box::new(Formula::Eq(
        Box::new(Formula::var_owned("_0_discr".into(), Sort::Int)),
        Box::new(Formula::Int(0)),
    )));
    let mut func = pair_wrapper_fn("gt", true, false, GT_PAIR_ENSURES);
    func.contracts.clear();
    func.postconditions = vec![Formula::Not(Box::new(Formula::And(vec![
        discr_ok.clone(),
        Formula::Ge(
            Box::new(Formula::var_owned(OK0.into(), Sort::Int)),
            Box::new(Formula::Add(
                Box::new(Formula::var_owned(OK1.into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
        ),
    ])))];
    assert!(
        postcondition_vcs(&func).is_empty(),
        "an arithmetic pair atom must not reach the refutable lane"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(details[0].contains(OK0) && details[0].contains(OK1), "{}", details[0]);

    let mut func = sign_wrapper_fn();
    func.contracts.clear();
    func.postconditions = vec![Formula::Not(Box::new(Formula::And(vec![
        discr_ok,
        Formula::Gt(
            Box::new(Formula::var_owned(SIGN.into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        ),
    ])))];
    assert!(
        postcondition_vcs(&func).is_empty(),
        "a sign atom against a nonzero constant must not reach the refutable lane"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(details[0].contains(SIGN), "{}", details[0]);
}
