use trust_types::UnwindEdge;

/// The Option/Expr carrier types, simplified: the recognizer only reads
/// the return type's `Adt` NAME, `Ty::Bool` on the guard dest, and the
/// newtype-u64 ref types on the sentinel guard args.
pub(crate) fn opt_ty() -> trust_types::Ty {
    trust_types::Ty::adt_enum(
        "std::option::Option",
        vec![
            trust_types::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            trust_types::VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), expr_ty())],
            },
        ],
    )
}
pub(crate) fn fvar_id_ty() -> trust_types::Ty {
    trust_types::Ty::adt(
        "expr::types::FVarId",
        vec![("0".into(), trust_types::Ty::Int { width: 64, signed: false })],
    )
}
pub(crate) fn expr_ty() -> trust_types::Ty {
    trust_types::Ty::adt(
        "expr::Expr",
        vec![("kind".into(), trust_types::Ty::Int { width: 64, signed: true })],
    )
}
pub(crate) fn ref_of(inner: trust_types::Ty, mutable: bool) -> trust_types::Ty {
    trust_types::Ty::Ref { mutable, inner: Box::new(inner) }
}

/// `<Abstractor as ExprFolderOpt>::fold_fvar_opt` — the Family-D shape:
/// `if id == self.id { Some(ek(ExprKind::BVar(self.depth))) } else { None }`.
/// Guard = `__trust_total_clone` sentinel (derived newtype-u64 `PartialEq`),
/// payload chain = field read → `ExprKind::BVar` ctor → `ek` call.
pub(crate) fn abstractor_fold_fvar_opt_func() -> trust_types::VerifiableFunction {
    use trust_types::{
        AggregateKind, BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, Statement,
        Terminator, Ty, VerifiableBody, VerifiableFunction,
    };
    let abstractor_ty = || {
        Ty::adt(
            "expr::subst::Abstractor",
            vec![
                ("id".into(), fvar_id_ty()),
                ("depth".into(), Ty::Int { width: 32, signed: false }),
            ],
        )
    };
    let ek_kind_ty = || {
        Ty::adt_enum(
            "expr::kind::ExprKind",
            vec![trust_types::VariantDef {
                name: "BVar".into(),
                discriminant: 0,
                fields: vec![("0".into(), Ty::Int { width: 32, signed: false })],
            }],
        )
    };
    let deref_field = |local: usize, f: usize| trust_types::Place {
        local,
        projections: vec![trust_types::Projection::Deref, trust_types::Projection::Field(f)],
    };
    VerifiableFunction {
        name: "fold_fvar_opt".into(),
        def_path:
            "<expr::subst::Abstractor as expr::visitor::opt::ExprFolderOpt>::fold_fvar_opt"
                .into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: opt_ty(), name: None },
                LocalDecl {
                    index: 1,
                    ty: ref_of(abstractor_ty(), true),
                    name: Some("self".into()),
                },
                LocalDecl { index: 2, ty: fvar_id_ty(), name: Some("id".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: ref_of(fvar_id_ty(), false), name: None },
                LocalDecl { index: 5, ty: ref_of(fvar_id_ty(), false), name: None },
                LocalDecl { index: 6, ty: expr_ty(), name: None },
                LocalDecl { index: 7, ty: ek_kind_ty(), name: None },
                LocalDecl { index: 8, ty: Ty::Int { width: 32, signed: false }, name: None },
            ],
            blocks: vec![
                // bb0: _4 = &_2; _5 = &(*_1).id; _3 = __trust_total_clone(_4, _5) → bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Ref { mutable: false, place: Place::local(2) },
                            span: Default::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::Ref { mutable: false, place: deref_field(1, 0) },
                            span: Default::default(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL
                            .into(),
                        args: vec![
                            Operand::Move(Place::local(4)),
                            Operand::Move(Place::local(5)),
                        ],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: Default::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                    },
                },
                // bb1: SwitchInt(_3) [0 → bb4] else bb2
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: Default::default(),
                    },
                },
                // bb2: _8 = (*_1).depth; _7 = ExprKind::BVar(_8); _6 = ek(_7) → bb3
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(8),
                            rvalue: Rvalue::Use(Operand::Copy(deref_field(1, 1))),
                            span: Default::default(),
                        },
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: "expr::kind::ExprKind".into(),
                                    variant: 0,
                                    active_field: None,
                                },
                                vec![Operand::Move(Place::local(8))],
                            ),
                            span: Default::default(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "expr::kind::ek".into(),
                        args: vec![Operand::Move(Place::local(7))],
                        dest: Place::local(6),
                        target: Some(BlockId(3)),
                        span: Default::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                    },
                },
                // bb3: _0 = Some(_6) → bb5
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "std::option::Option".into(),
                                variant: 1,
                                active_field: None,
                            },
                            vec![Operand::Move(Place::local(6))],
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                // bb4: _0 = None → bb5
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "std::option::Option".into(),
                                variant: 0,
                                active_field: None,
                            },
                            vec![],
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: opt_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `<FVarSubst as ExprFolderOpt>::fold_fvar_opt` — the field-clone
/// Family-D variant: `Some(self.replacement.clone())` on the sentinel
/// guard's true edge. The replacement snapshot is a shared reference and
/// remains an opaque call argument; it is never scalarized.
pub(crate) fn fvarsubst_fold_fvar_opt_func() -> trust_types::VerifiableFunction {
    use trust_types::{Operand, Place, Rvalue, Statement, Terminator, Ty};

    let mut func = abstractor_fold_fvar_opt_func();
    func.def_path =
        "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::fold_fvar_opt"
            .into();
    func.body.locals[1].ty = ref_of(
        Ty::adt(
            "expr::subst::FVarSubst",
            vec![("id".into(), fvar_id_ty()), ("replacement".into(), ref_of(expr_ty(), false))],
        ),
        true,
    );
    func.body.locals[7].ty = ref_of(expr_ty(), false);
    func.body.blocks[2].stmts = vec![Statement::Assign {
        place: Place::local(7),
        rvalue: Rvalue::Use(Operand::Copy(trust_types::Place {
            local: 1,
            projections: vec![
                trust_types::Projection::Deref,
                trust_types::Projection::Field(1),
            ],
        })),
        span: Default::default(),
    }];
    func.body.blocks[2].terminator = Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: "std::clone::Clone::clone".into(),
        args: vec![Operand::Copy(Place::local(7))],
        dest: Place::local(6),
        target: Some(trust_types::BlockId(3)),
        span: Default::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
    };
    func
}

/// `<Lifter as ExprFolderOpt>::fold_bvar_opt` — the Family-B shape:
/// `if idx >= self.start { Some(ek(ExprKind::BVar(checked_add_u32(idx,
/// self.amount, "...")))) } else { None }`. Guard = REAL `Ge` comparison
/// (param vs entry field read).
pub(crate) fn lifter_fold_bvar_opt_func() -> trust_types::VerifiableFunction {
    use trust_types::{
        AggregateKind, BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
        Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };
    let u32t = || Ty::Int { width: 32, signed: false };
    let lifter_ty = || {
        Ty::adt(
            "expr::subst::Lifter",
            vec![("start".into(), u32t()), ("amount".into(), u32t())],
        )
    };
    let ek_kind_ty = || {
        Ty::adt_enum(
            "expr::kind::ExprKind",
            vec![trust_types::VariantDef {
                name: "BVar".into(),
                discriminant: 0,
                fields: vec![("0".into(), u32t())],
            }],
        )
    };
    let deref_field = |local: usize, f: usize| trust_types::Place {
        local,
        projections: vec![trust_types::Projection::Deref, trust_types::Projection::Field(f)],
    };
    VerifiableFunction {
        name: "fold_bvar_opt".into(),
        def_path: "<expr::subst::Lifter as expr::visitor::opt::ExprFolderOpt>::fold_bvar_opt"
            .into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: opt_ty(), name: None },
                LocalDecl {
                    index: 1,
                    ty: ref_of(lifter_ty(), true),
                    name: Some("self".into()),
                },
                LocalDecl { index: 2, ty: u32t(), name: Some("idx".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: u32t(), name: None },
                LocalDecl { index: 5, ty: expr_ty(), name: None },
                LocalDecl { index: 6, ty: ek_kind_ty(), name: None },
                LocalDecl { index: 7, ty: u32t(), name: None },
                LocalDecl { index: 8, ty: u32t(), name: None },
            ],
            blocks: vec![
                // bb0: _4 = (*_1).start; _3 = Ge(_2, _4); switch [0→bb4] else bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(deref_field(1, 0))),
                            span: Default::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                trust_types::BinOp::Ge,
                                Operand::Copy(Place::local(2)),
                                Operand::Move(Place::local(4)),
                            ),
                            span: Default::default(),
                        },
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: Default::default(),
                    },
                },
                // bb1: _8 = (*_1).amount; _7 = checked_add_u32(_2, _8, "…") → bb2
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(8),
                        rvalue: Rvalue::Use(Operand::Copy(deref_field(1, 1))),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "expr::checked_add_u32".into(),
                        args: vec![
                            Operand::Copy(Place::local(2)),
                            Operand::Move(Place::local(8)),
                            Operand::Constant(ConstValue::Str {
                                bytes: b"lift bvar index".to_vec(),
                            }),
                        ],
                        dest: Place::local(7),
                        target: Some(BlockId(2)),
                        span: Default::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                    },
                },
                // bb2: _6 = ExprKind::BVar(_7); _5 = ek(_6) → bb3
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "expr::kind::ExprKind".into(),
                                variant: 0,
                                active_field: None,
                            },
                            vec![Operand::Move(Place::local(7))],
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "expr::kind::ek".into(),
                        args: vec![Operand::Move(Place::local(6))],
                        dest: Place::local(5),
                        target: Some(BlockId(3)),
                        span: Default::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                    },
                },
                // bb3: _0 = Some(_5) → bb5
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "std::option::Option".into(),
                                variant: 1,
                                active_field: None,
                            },
                            vec![Operand::Move(Place::local(5))],
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                // bb4: _0 = None → bb5
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "std::option::Option".into(),
                                variant: 0,
                                active_field: None,
                            },
                            vec![],
                        ),
                        span: Default::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: opt_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}
