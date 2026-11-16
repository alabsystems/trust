//! TINV step 7.4: the point enumeration, one row per rule, on hand-built bodies and on
//! the step-0(a) real-MIR fixture.

use std::collections::HashSet;

use trust_types::{
    AggregateKind, BasicBlock, BlockId, CalleeIdentity, ConstValue, Formula, LocalDecl, Operand,
    Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, TypeInvariantPoint,
    TypeInvariantSite, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::super::unwind::{NoExactModels, URefusal};
use super::super::{
    CandidateConjunct, FieldTerm, Sigma, TinvBodyFacts, TinvType, field_var, instantiate,
};
use super::*;

fn adt(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: name.into(),
        fields: fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect::<Vec<_>>().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn vec_ty() -> Ty {
    Ty::Seq { elem: Box::new(Ty::Int { width: 8, signed: false }), drop_auth: None }
}

/// `c::S { v: Vec<u8>, k: u64 }`.
fn s_ty() -> Ty {
    adt("c::S", vec![("v", vec_ty()), ("k", u64_ty())])
}

/// `c::Owner(S)`.
fn owner_ty() -> Ty {
    adt("c::Owner", vec![("0", s_ty())])
}

fn mut_ref(t: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(t) }
}

fn shared_ref(t: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(t) }
}

fn tinv() -> TinvType {
    TinvType {
        def_path: "c::S".into(),
        fields: vec![("v".into(), vec_ty()), ("k".into(), u64_ty())],
        conjuncts: Vec::new(),
    }
}

fn func(locals: Vec<Ty>, arg_count: usize, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "c::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: locals[0].clone(),
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks,
            arg_count,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn blk(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn konst(v: i128) -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Int(v)))
}

fn place(local: usize, projections: Vec<Projection>) -> Place {
    Place { local, projections }
}

/// `*_l`.
fn pointee(local: usize) -> Place {
    place(local, vec![Projection::Deref])
}

/// `(*_l).k` (field 1 of `S`).
fn pointee_k(local: usize) -> Place {
    place(local, vec![Projection::Deref, Projection::Field(1)])
}

fn s_aggregate(ops: Vec<Operand>) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt { name: "c::S".into(), variant: 0, active_field: None, args: None },
        ops,
    )
}

fn ident(n: u32) -> CalleeIdentity {
    CalleeIdentity { stable_crate_id: 1, def_index: n, substs_digest: [0, 0] }
}

fn call(
    args: Vec<Operand>,
    dest: Place,
    target: Option<usize>,
    id: Option<CalleeIdentity>,
) -> Terminator {
    Terminator::Call {
        func: "g".into(),
        args,
        dest,
        target: target.map(BlockId),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Continue,
        callee_identity: id,
        callee_key: None,
    }
}

fn assert_term(cond: usize, target: usize) -> Terminator {
    Terminator::Assert {
        cond: Operand::Copy(Place::local(cond)),
        expected: true,
        msg: trust_types::AssertMessage::BoundsCheck,
        target: BlockId(target),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Continue,
    }
}

fn drop_term(p: Place, target: usize) -> Terminator {
    Terminator::Drop {
        place: p,
        target: BlockId(target),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Continue,
    }
}

const INV: u32 = 7;

fn run_with(
    f: &VerifiableFunction,
    may_drop: &dyn Fn(&Ty) -> bool,
) -> Result<Vec<TinvPointRow>, TinvObligationRefusal> {
    let ty = tinv();
    let inventory: HashSet<CalleeIdentity> = [ident(INV)].into_iter().collect();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: may_drop,
    };
    obligation_points(f, None, &inp)
}

fn run(f: &VerifiableFunction) -> Result<Vec<TinvPointRow>, TinvObligationRefusal> {
    run_with(f, &|_| true)
}

type Key = (TypeInvariantPoint, usize, usize, Place);

fn keys(rows: &[TinvPointRow]) -> Vec<Key> {
    rows.iter().map(|r| (r.point, r.site.block, r.site.statement_index, r.root.clone())).collect()
}

fn key(point: TypeInvariantPoint, block: usize, stmt: usize, root: Place) -> Key {
    (point, block, stmt, root)
}

use TypeInvariantPoint::{
    Call as C, Drop as D, Establish as E, Move as M, Return as R, Unwind as U,
};

#[test]
fn an_aggregate_of_s_is_an_establish_point_with_its_operands_as_sigma() {
    // _1: Vec<u8>, _2: u64 (params); _0 = S { v: move _1, k: copy _2 }; return.
    let ops = vec![Operand::Move(Place::local(1)), Operand::Copy(Place::local(2))];
    let f = func(
        vec![s_ty(), vec_ty(), u64_ty()],
        2,
        vec![blk(0, vec![assign(Place::local(0), s_aggregate(ops.clone()))], Terminator::Return)],
    );
    let rows = run(&f).expect("points");
    // The aggregate cleans `_0`: E is owed, R is not.
    assert_eq!(keys(&rows), vec![key(E, 0, 0, Place::local(0))]);
    assert_eq!(rows[0].row_point, 0);
    let SigmaSource::AggregateOperands(got) = &rows[0].sigma_src else { panic!("{:?}", rows[0]) };
    assert_eq!(format!("{got:?}"), format!("{ops:?}"));
    // σ from the operands: `v` has a Len and no Value, `k` a Value and no Len.
    let sigma = sigma_of_operands(&f, &tinv(), got);
    assert!(sigma.value[0].is_none() && sigma.len[0].is_some());
    assert!(sigma.value[1].is_some() && sigma.len[1].is_none());
    let c = CandidateConjunct {
        id: 0,
        formula: Formula::Le(
            Box::new(field_var(FieldTerm::Value(1))),
            Box::new(field_var(FieldTerm::Len(0))),
        ),
    };
    let inst = instantiate(&c, &sigma).expect("k <= len(v) instantiates");
    assert_eq!(
        inst,
        Formula::Le(
            Box::new(sigma.value[1].clone().unwrap()),
            Box::new(sigma.len[0].clone().unwrap())
        )
    );
}

#[test]
fn a_mut_self_method_writing_a_field_owes_r_for_the_param_root() {
    // _1: &mut S; (*_1).k = 5; return.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty())],
        1,
        vec![blk(0, vec![assign(pointee_k(1), konst(5))], Terminator::Return)],
    );
    let rows = run(&f).expect("points");
    assert_eq!(keys(&rows), vec![key(R, 0, 1, pointee(1))]);
    assert_eq!(rows[0].row_point, usize::MAX);
    assert!(matches!(rows[0].sigma_src, SigmaSource::Root));
    assert!(matches!(rows[0].state, TinvStateSpec::At));
}

#[test]
fn a_method_that_does_not_write_s_owes_nothing() {
    // _2 = copy (*_1).k; _3 = &(*_1).v; return.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty()), u64_ty(), shared_ref(vec_ty())],
        1,
        vec![blk(
            0,
            vec![
                assign(Place::local(2), Rvalue::Use(Operand::Copy(pointee_k(1)))),
                assign(
                    Place::local(3),
                    Rvalue::Ref {
                        mutable: false,
                        place: place(1, vec![Projection::Deref, Projection::Field(0)]),
                    },
                ),
            ],
            Terminator::Return,
        )],
    );
    assert!(run(&f).expect("points").is_empty());
}

#[test]
fn re_aggregation_kills_the_window() {
    // (*_1).k = 9; (*_1) = S { v: move _2, k: const 0 }; return.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty()), vec_ty()],
        1,
        vec![blk(
            0,
            vec![
                assign(pointee_k(1), konst(9)),
                assign(
                    pointee(1),
                    s_aggregate(vec![
                        Operand::Move(Place::local(2)),
                        Operand::Constant(ConstValue::Int(0)),
                    ]),
                ),
            ],
            Terminator::Return,
        )],
    );
    assert_eq!(keys(&run(&f).expect("points")), vec![key(E, 0, 1, pointee(1))]);
}

#[test]
fn a_clean_transfer_kills_and_a_dirty_one_owes_m_then_r() {
    // _2 = S { move _1, 0 }; [_2.k = 9;] _0 = move _2; return.
    let body = |dirty: bool| {
        let mut stmts = vec![assign(
            Place::local(2),
            s_aggregate(vec![
                Operand::Move(Place::local(1)),
                Operand::Constant(ConstValue::Int(0)),
            ]),
        )];
        if dirty {
            stmts.push(assign(place(2, vec![Projection::Field(1)]), konst(9)));
        }
        stmts.push(assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(2)))));
        func(vec![s_ty(), vec_ty(), s_ty()], 1, vec![blk(0, stmts, Terminator::Return)])
    };
    assert_eq!(keys(&run(&body(false)).expect("points")), vec![key(E, 0, 0, Place::local(2))]);
    assert_eq!(
        keys(&run(&body(true)).expect("points")),
        vec![
            key(E, 0, 0, Place::local(2)),
            key(M, 0, 2, Place::local(2)),
            key(R, 0, 3, Place::local(0))
        ]
    );
}

#[test]
fn a_dirty_value_wrapped_in_another_aggregate_owes_m() {
    // Rail 16's `Some(p)`: _2 = S { move _1, 0 }; _2.k = 9; _0 = Some(move _2); return.
    let option = adt("core::option::Option", vec![("0", s_ty())]);
    let some = Rvalue::Aggregate(
        AggregateKind::Adt {
            name: "core::option::Option".into(),
            variant: 1,
            active_field: None,
            args: None,
        },
        vec![Operand::Move(Place::local(2))],
    );
    let f = func(
        vec![option, vec_ty(), s_ty()],
        1,
        vec![blk(
            0,
            vec![
                assign(
                    Place::local(2),
                    s_aggregate(vec![
                        Operand::Move(Place::local(1)),
                        Operand::Constant(ConstValue::Int(0)),
                    ]),
                ),
                assign(place(2, vec![Projection::Field(1)]), konst(9)),
                assign(Place::local(0), some),
            ],
            Terminator::Return,
        )],
    );
    assert_eq!(
        keys(&run(&f).expect("points")),
        vec![key(E, 0, 0, Place::local(2)), key(M, 0, 2, Place::local(2))]
    );
}

/// _1: &mut S; [(*_1).k = 5;] _2 = &mut (*_1); g(move _2) -> bb1; bb1: return.
fn pass_through(dirty_first: bool, callee: Option<CalleeIdentity>) -> VerifiableFunction {
    let mut stmts = Vec::new();
    if dirty_first {
        stmts.push(assign(pointee_k(1), konst(5)));
    }
    stmts.push(assign(Place::local(2), Rvalue::Ref { mutable: true, place: pointee(1) }));
    func(
        vec![Ty::Unit, mut_ref(s_ty()), mut_ref(s_ty()), Ty::Unit],
        1,
        vec![
            blk(
                0,
                stmts,
                call(vec![Operand::Move(Place::local(2))], Place::local(3), Some(1), callee),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    )
}

#[test]
fn a_pass_through_reborrow_to_an_inventory_callee_is_a_c_point_and_cleans_the_root() {
    let rows = run(&pass_through(true, Some(ident(INV)))).expect("points");
    // M at the whole reborrow of the dirty root, C at the call; the call discharges U for
    // the passed root and kills the window, so no U and no R.
    assert_eq!(keys(&rows), vec![key(M, 0, 1, pointee(1)), key(C, 0, 2, pointee(1))]);
    // A clean root still owes C (TINV-4), and nothing else.
    assert_eq!(
        keys(&run(&pass_through(false, Some(ident(INV)))).expect("points")),
        vec![key(C, 0, 1, pointee(1))]
    );
}

#[test]
fn the_same_reborrow_to_a_callee_outside_the_inventory_owes_u_with_havoc_and_r() {
    for callee in [None, Some(ident(INV + 1))] {
        let rows = run(&pass_through(false, callee)).expect("points");
        // Clean before the call, but the callee may write it before it panics: U is owed
        // in the havocked pre-call state, and R after the call.
        assert_eq!(
            keys(&rows),
            vec![key(C, 0, 1, pointee(1)), key(U, 0, 1, pointee(1)), key(R, 1, 0, pointee(1))],
            "{callee:?}"
        );
        let u = &rows[1];
        assert!(
            matches!(&u.state, TinvStateSpec::UnwindCallHavoc { inventory_passed } if inventory_passed.is_empty())
        );
        assert!(u.failure.is_none());
    }
}

#[test]
fn a_field_borrow_is_sticky_and_an_inventory_call_does_not_clean_it() {
    // _2 = &mut (*_1).k; h(move _2) -> bb1 [inventory]; bb1: g(move _1) -> bb2 [inventory];
    // bb2: return.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty()), mut_ref(u64_ty()), Ty::Unit],
        1,
        vec![
            blk(
                0,
                vec![assign(Place::local(2), Rvalue::Ref { mutable: true, place: pointee_k(1) })],
                call(
                    vec![Operand::Move(Place::local(2))],
                    Place::local(3),
                    Some(1),
                    Some(ident(INV)),
                ),
            ),
            blk(
                1,
                vec![],
                call(
                    vec![Operand::Move(Place::local(1))],
                    Place::local(3),
                    Some(2),
                    Some(ident(INV)),
                ),
            ),
            blk(2, vec![], Terminator::Return),
        ],
    );
    let rows = keys(&run(&f).expect("points"));
    assert!(rows.contains(&key(R, 2, 0, pointee(1))), "{rows:?}");
    // The first call receives no `S` root, so it does not discharge `*_1`.
    assert!(rows.contains(&key(U, 0, 1, pointee(1))), "{rows:?}");
    // The second receives it: C, and its U is discharged.
    assert!(rows.contains(&key(C, 1, 0, pointee(1))), "{rows:?}");
    assert!(!rows.contains(&key(U, 1, 0, pointee(1))), "{rows:?}");
}

#[test]
fn a_write_through_a_reborrow_dirties_the_root_it_aliases() {
    // _2 = &mut (*_1); (*_2).k = 5; return.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty()), mut_ref(s_ty())],
        1,
        vec![blk(
            0,
            vec![
                assign(Place::local(2), Rvalue::Ref { mutable: true, place: pointee(1) }),
                assign(pointee_k(2), konst(5)),
            ],
            Terminator::Return,
        )],
    );
    assert_eq!(keys(&run(&f).expect("points")), vec![key(R, 0, 2, pointee(1))]);
}

#[test]
fn u_is_owed_at_asserts_and_calls_inside_the_window_and_not_outside() {
    // bb0: f() -> bb1 (clean); bb1: (*_1).k = 5; assert(_2) -> bb2; bb2: f() -> bb3;
    // bb3: return.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty()), Ty::Bool, Ty::Unit],
        1,
        vec![
            blk(0, vec![], call(vec![], Place::local(3), Some(1), None)),
            blk(1, vec![assign(pointee_k(1), konst(5))], assert_term(2, 2)),
            blk(2, vec![], call(vec![], Place::local(3), Some(3), None)),
            blk(3, vec![], Terminator::Return),
        ],
    );
    let rows = run(&f).expect("points");
    assert_eq!(
        keys(&rows),
        vec![key(U, 1, 1, pointee(1)), key(U, 2, 0, pointee(1)), key(R, 3, 0, pointee(1))]
    );
    let assert_row = &rows[0];
    assert!(matches!(assert_row.state, TinvStateSpec::At));
    assert!(matches!(&assert_row.failure, Some((Operand::Copy(p), true)) if *p == Place::local(2)));
    assert!(matches!(rows[1].state, TinvStateSpec::UnwindCallHavoc { .. }));
}

/// _1: Owner (a local); _1.0.k = 7; may_panic() -> bb1; bb1: drop(_1) -> bb2; bb2: return.
fn owner_body() -> VerifiableFunction {
    func(
        vec![Ty::Unit, owner_ty(), Ty::Unit],
        0,
        vec![
            blk(
                0,
                vec![assign(place(1, vec![Projection::Field(0), Projection::Field(1)]), konst(7))],
                call(vec![], Place::local(2), Some(1), None),
            ),
            blk(1, vec![], drop_term(Place::local(1), 2)),
            blk(2, vec![], Terminator::Return),
        ],
    )
}

#[test]
fn u_on_a_local_root_is_asked_of_the_owning_type_and_drop_of_the_dropped_type() {
    let root = place(1, vec![Projection::Field(0)]);
    let is_owner = |t: &Ty| matches!(t, Ty::Adt { name, .. } if name == "c::Owner");
    // `Owner::drop` runs in cleanup and observes the dirty `o.0` (rail 8 on unwind), even
    // though `S` itself has no Drop.
    let rows = run_with(&owner_body(), &is_owner).expect("points");
    assert_eq!(
        keys(&rows),
        vec![key(U, 0, 1, root.clone()), key(U, 1, 0, root.clone()), key(D, 1, 0, root.clone())]
    );
    assert!(matches!(&rows[1].state, TinvStateSpec::UnwindDropHavoc(p) if *p == Place::local(1)));
    // Asking of `S` instead would miss it: an `S`-only answer owes nothing.
    let is_s_only = |t: &Ty| matches!(t, Ty::Adt { name, .. } if name == "c::S");
    assert!(run_with(&owner_body(), &is_s_only).expect("points").is_empty());
    assert!(run_with(&owner_body(), &|_| false).expect("points").is_empty());
}

#[test]
fn unsupported_root_shapes_refuse() {
    // f(move _2) with `_2: &&S` / `&mut Owner` / `Option<&mut S>`.
    let option = adt("core::option::Option", vec![("0", mut_ref(s_ty()))]);
    for arg_ty in [shared_ref(shared_ref(s_ty())), mut_ref(owner_ty()), option] {
        let f = func(
            vec![Ty::Unit, arg_ty.clone(), Ty::Unit],
            1,
            vec![
                blk(
                    0,
                    vec![],
                    call(vec![Operand::Move(Place::local(1))], Place::local(2), Some(1), None),
                ),
                blk(1, vec![], Terminator::Return),
            ],
        );
        assert!(
            matches!(
                run(&f),
                Err(TinvObligationRefusal::RootShape {
                    site: TypeInvariantSite { block: 0, statement_index: 0 },
                    ..
                })
            ),
            "{arg_ty:?}: {:?}",
            run(&f)
        );
    }
}

#[test]
fn a_reborrow_argument_without_a_unique_definition_is_unresolved() {
    // bb0: switch -> bb1 | bb2; bb1/bb2: _2 = &mut (*_1); goto bb3; bb3: g(move _2).
    let reborrow = || assign(Place::local(2), Rvalue::Ref { mutable: true, place: pointee(1) });
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty()), mut_ref(s_ty()), Ty::Unit, u64_ty()],
        1,
        vec![
            blk(
                0,
                vec![],
                Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(4)),
                    targets: vec![(0, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            blk(1, vec![reborrow()], Terminator::Goto(BlockId(3))),
            blk(2, vec![reborrow()], Terminator::Goto(BlockId(3))),
            blk(
                3,
                vec![],
                call(vec![Operand::Move(Place::local(2))], Place::local(3), Some(4), None),
            ),
            blk(4, vec![], Terminator::Return),
        ],
    );
    assert_eq!(
        run(&f).map(|r| keys(&r)),
        Err(TinvObligationRefusal::UnresolvedRoot {
            site: TypeInvariantSite { block: 3, statement_index: 0 }
        })
    );
}

#[test]
fn a_write_through_a_reassigned_reference_parameter_is_unresolved() {
    // fn f(mut a: &mut S, b: &mut S) { a = b; a.k = 5; } — the write lands in `*b`, so
    // `*_1` is not a fixed identity.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty()), mut_ref(s_ty())],
        2,
        vec![blk(
            0,
            vec![
                assign(Place::local(1), Rvalue::Use(Operand::Move(Place::local(2)))),
                assign(pointee_k(1), konst(5)),
            ],
            Terminator::Return,
        )],
    );
    assert!(matches!(run(&f), Err(TinvObligationRefusal::UnresolvedRoot { .. })), "{:?}", run(&f));
}

#[test]
fn a_raw_pointer_write_refuses_the_type() {
    // _1: *mut S; (*_1).k = 0.
    let f = func(
        vec![Ty::Unit, Ty::RawPtr { mutable: true, pointee: Box::new(s_ty()) }],
        1,
        vec![blk(0, vec![assign(pointee_k(1), konst(0))], Terminator::Return)],
    );
    assert!(matches!(run(&f), Err(TinvObligationRefusal::Write(_))), "{:?}", run(&f));
}

#[test]
fn lost_edges_tail_calls_and_fact_disagreements_refuse() {
    let opaque = func(
        vec![Ty::Unit],
        0,
        vec![blk(
            0,
            vec![],
            Terminator::Opaque {
                kind: "InlineAsm".into(),
                targets: vec![],
                span: SourceSpan::default(),
            },
        )],
    );
    // An inline asm is also an unlocatable write; either refusal withholds.
    assert!(run(&opaque).is_err());
    let tail = func(
        vec![Ty::Unit],
        0,
        vec![blk(
            0,
            vec![],
            Terminator::TailCall {
                func: "g".into(),
                args: vec![],
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: None,
            },
        )],
    );
    assert_eq!(run(&tail).map(|r| keys(&r)), Err(TinvObligationRefusal::U(URefusal::TailCall)));
    let plain = func(vec![Ty::Unit], 0, vec![blk(0, vec![], Terminator::Return)]);
    let ty = tinv();
    let inventory = HashSet::new();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    let facts = TinvBodyFacts { block_count: 2, ..Default::default() };
    assert!(matches!(
        obligation_points(&plain, Some(&facts), &inp),
        Err(TinvObligationRefusal::CrossCheck(_))
    ));
    let facts = TinvBodyFacts { block_count: 1, ..Default::default() };
    assert!(obligation_points(&plain, Some(&facts), &inp).expect("agrees").is_empty());
}

#[test]
fn a_cleanup_region_call_receiving_s_refuses() {
    // bb0: f() -> bb1, unwind -> bb2; bb1: return; bb2 (cleanup): g(move _1) -> bb3; bb3: resume.
    let mut first = call(vec![], Place::local(2), Some(1), None);
    if let Terminator::Call { unwind, .. } = &mut first {
        *unwind = UnwindEdge::Cleanup(BlockId(2));
    }
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty()), Ty::Unit],
        1,
        vec![
            blk(0, vec![], first),
            blk(1, vec![], Terminator::Return),
            blk(
                2,
                vec![],
                call(vec![Operand::Move(Place::local(1))], Place::local(2), Some(3), None),
            ),
            blk(3, vec![], Terminator::Resume),
        ],
    );
    assert!(matches!(run(&f), Err(TinvObligationRefusal::RootShape { .. })), "{:?}", run(&f));
}

#[test]
fn instantiate_refuses_foreign_variables_missing_terms_and_sort_mismatches() {
    let int = |n: &str| Formula::var(n, Sort::Int);
    let sigma = Sigma {
        value: vec![None, Some(int("self*.1")), Some(Formula::var("flag", Sort::Bool))],
        len: vec![Some(int("self*.0")), None, None],
    };
    let le = |a: Formula, b: Formula| CandidateConjunct {
        id: 3,
        formula: Formula::Le(Box::new(a), Box::new(b)),
    };
    let v = |i| field_var(FieldTerm::Value(i));
    let l = |i| field_var(FieldTerm::Len(i));
    assert_eq!(
        instantiate(&le(v(1), l(0)), &sigma),
        Some(Formula::Le(Box::new(int("self*.1")), Box::new(int("self*.0"))))
    );
    // A free variable that is not a placeholder.
    assert_eq!(instantiate(&le(int("x"), l(0)), &sigma), None);
    // A placeholder spelled with another sort is not a placeholder.
    assert_eq!(instantiate(&le(Formula::var("$tinv_v1", Sort::Bool), l(0)), &sigma), None);
    assert_eq!(instantiate(&le(Formula::var("$tinv_v01", Sort::Int), l(0)), &sigma), None);
    // Missing terms: a None slot and an index past σ.
    assert_eq!(instantiate(&le(v(0), l(0)), &sigma), None);
    assert_eq!(instantiate(&le(v(1), l(1)), &sigma), None);
    assert_eq!(instantiate(&le(v(9), l(0)), &sigma), None);
    // A sort mismatch: the term is Bool-sorted.
    assert_eq!(instantiate(&le(v(2), l(0)), &sigma), None);
    // A binder is never walked.
    let under_binder = CandidateConjunct {
        id: 4,
        formula: Formula::Forall(vec![], Box::new(le(v(1), l(0)).formula)),
    };
    assert_eq!(instantiate(&under_binder, &sigma), None);
    // Deep conjuncts are walked without recursion.
    let mut deep = v(1);
    for _ in 0..3000 {
        deep = Formula::Add(Box::new(deep), Box::new(Formula::Int(1)));
    }
    let got = instantiate(&le(deep, l(0)), &sigma).expect("deep conjunct");
    let Formula::Le(lhs, _) = &got else { panic!() };
    let mut at = lhs.as_ref();
    let mut depth = 0;
    while let Formula::Add(a, _) = at {
        at = a.as_ref();
        depth += 1;
    }
    assert_eq!((depth, at), (3000, &int("self*.1")));
}

#[test]
fn post_call_assumptions_only_at_single_predecessor_targets_of_inventory_calls() {
    // bb0: switch -> bb1 | bb2; bb1: _3 = &mut *_1; g(move _3) -> bb3 [inv];
    // bb2: goto bb3; bb3: _4 = &mut *_1; g(move _4) -> bb4 [inv]; bb4: _5 = &mut *_1;
    // h(move _5) -> bb5 [not inv]; bb5: return.
    let reborrow = |l| assign(Place::local(l), Rvalue::Ref { mutable: true, place: pointee(1) });
    let f = func(
        vec![
            Ty::Unit,
            mut_ref(s_ty()),
            u64_ty(),
            mut_ref(s_ty()),
            mut_ref(s_ty()),
            mut_ref(s_ty()),
            Ty::Unit,
        ],
        1,
        vec![
            blk(
                0,
                vec![],
                Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            blk(
                1,
                vec![reborrow(3)],
                call(
                    vec![Operand::Move(Place::local(3))],
                    Place::local(6),
                    Some(3),
                    Some(ident(INV)),
                ),
            ),
            blk(2, vec![], Terminator::Goto(BlockId(3))),
            blk(
                3,
                vec![reborrow(4)],
                call(
                    vec![Operand::Move(Place::local(4))],
                    Place::local(6),
                    Some(4),
                    Some(ident(INV)),
                ),
            ),
            blk(
                4,
                vec![reborrow(5)],
                call(
                    vec![Operand::Move(Place::local(5))],
                    Place::local(6),
                    Some(5),
                    Some(ident(INV + 1)),
                ),
            ),
            blk(5, vec![], Terminator::Return),
        ],
    );
    let ty = tinv();
    let inventory: HashSet<CalleeIdentity> = [ident(INV)].into_iter().collect();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    assert_eq!(
        post_call_assumption_points(&f, &inp),
        vec![PostCall {
            call_block: BlockId(3),
            target: BlockId(4),
            root: pointee(1),
            kind: PostCallRoot::Arg,
        }]
    );
    // An unwind edge into the target makes it a join: no fact.
    let mut joined = f.clone();
    if let Terminator::Call { unwind, .. } = &mut joined.body.blocks[1].terminator {
        *unwind = UnwindEdge::Cleanup(BlockId(4));
    }
    assert!(post_call_assumption_points(&joined, &inp).is_empty());
}

/// The step-0(a) fixture (`a::S { v: Vec<u8>, k: usize }`, `rebind(&mut self)` writing
/// `self.k` at bb2[0]); see `generate/tinv_entry_rename_tests.rs`.
fn load_fixture() -> VerifiableFunction {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/tinv_mut_pointee_entry_rename_mir.json"
    );
    serde_json::from_str(&std::fs::read_to_string(path).expect("fixture")).expect("deserialize")
}

#[test]
fn real_mir_rebind_owes_u_after_the_write_and_r_for_the_self_root() {
    let f = load_fixture();
    let usize_ty = f.body.locals[5].ty.clone();
    let ty = TinvType {
        def_path: "a::S".into(),
        fields: vec![("v".into(), vec_ty()), ("k".into(), usize_ty)],
        conjuncts: Vec::new(),
    };
    let inventory = HashSet::new();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    let rows = obligation_points(&f, None, &inp).expect("points");
    // The calls at bb0 and bb1 run before the write (clean: no U); the `Index::index` call
    // at bb2 runs inside the window; the Return at bb3 owes R. No call receives `S`.
    assert_eq!(keys(&rows), vec![key(U, 2, 3, pointee(1)), key(R, 3, 2, pointee(1))]);
    // σ of `*_1` is the walk's unversioned spelling.
    let sigma = sigma_of_root(&f, &ty, &pointee(1));
    let c = CandidateConjunct {
        id: 0,
        formula: Formula::Lt(
            Box::new(field_var(FieldTerm::Value(1))),
            Box::new(field_var(FieldTerm::Len(0))),
        ),
    };
    let inst = format!("{:?}", instantiate(&c, &sigma).expect("k < len(v)"));
    assert!(inst.contains("self*.1") && inst.contains("self*.0"), "{inst}");
}

/// Adversarial review (2026-10-05): optimized MIR folds `S { .. }` into a constant that no
/// aggregate constructs, so it owes no E; any constant that may hold an `S` refuses.
#[test]
fn a_constant_that_may_hold_s_refuses() {
    let call_with = |arg: ConstValue| {
        func(
            vec![Ty::Unit, Ty::Unit],
            0,
            vec![
                blk(0, vec![], call(vec![Operand::Constant(arg)], Place::local(1), Some(1), None)),
                blk(1, vec![], Terminator::Return),
            ],
        )
    };
    // `use_s(const S {{ .. }})`: an opaque constant argument, or a scalar-field struct
    // constant naming S.
    for arg in [
        ConstValue::opaque_const(),
        ConstValue::struct_scalar_fields_ref("c::S", vec![ConstValue::Int(1)]),
    ] {
        assert!(
            matches!(run(&call_with(arg.clone())), Err(TinvObligationRefusal::Write(_))),
            "{arg:?}"
        );
    }
    // Scalars and a struct constant of another type hold no S.
    for arg in
        [ConstValue::Int(3), ConstValue::struct_scalar_fields_ref("c::T", vec![ConstValue::Int(1)])]
    {
        assert!(run(&call_with(arg.clone())).is_ok(), "{arg:?}");
    }
    // `_1 = const <opaque>` into an S-typed local refuses; into a u64 local it does not.
    let store = |ty: Ty| {
        func(
            vec![Ty::Unit, ty],
            0,
            vec![blk(
                0,
                vec![assign(
                    Place::local(1),
                    Rvalue::Use(Operand::Constant(ConstValue::opaque_const())),
                )],
                Terminator::Return,
            )],
        )
    };
    assert!(matches!(run(&store(s_ty())), Err(TinvObligationRefusal::Write(_))));
    assert!(run(&store(u64_ty())).is_ok());
}

/// Adversarial review (2026-10-05): a write into a Box-owned `S` goes through a fresh
/// raw temp per deref site, never linked to the box, so v1 refuses such a root.
#[test]
fn a_root_reached_through_a_box_temp_refuses() {
    let raw_s = Ty::RawPtr { mutable: true, pointee: Box::new(s_ty()) };
    let nonnull = adt("core::ptr::non_null::NonNull", vec![("pointer", raw_s.clone())]);
    let unique = adt("core::ptr::unique::Unique", vec![("pointer", nonnull)]);
    let mut boxed = adt("alloc::boxed::Box", vec![("0", unique)]);
    if let Ty::Adt { adt_kind, .. } = &mut boxed {
        *adt_kind = Some(trust_types::AdtKind::Struct);
    }
    // _1: Box<S>; _2 = Cast(copy _1.0.0, *mut S); (*_2).k = 0.
    let f = func(
        vec![Ty::Unit, boxed, raw_s.clone()],
        1,
        vec![blk(
            0,
            vec![
                assign(
                    Place::local(2),
                    Rvalue::Cast(
                        Operand::Copy(place(1, vec![Projection::Field(0), Projection::Field(0)])),
                        raw_s,
                    ),
                ),
                assign(place(2, vec![Projection::Deref, Projection::Field(1)]), konst(0)),
            ],
            Terminator::Return,
        )],
    );
    assert!(matches!(run(&f), Err(TinvObligationRefusal::RootShape { .. })), "{:?}", run(&f));
}

/// Decision TINV-32: the census's per-body constant evidence (`TinvBodyFacts::
/// constants_may_hold`) clears an opaque constant at the mint as at synthesis, per type,
/// and never where the extraction says the constant's position is (or reaches) `S`.
#[test]
fn constant_evidence_clears_an_opaque_call_argument_at_the_mint() {
    let ty = tinv();
    let name = ty.def_path.clone();
    let inventory: HashSet<CalleeIdentity> = [ident(INV)].into_iter().collect();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    let with = |held: Option<Vec<&str>>, blocks: usize| TinvBodyFacts {
        block_count: blocks,
        constants_may_hold: held.map(|h| h.into_iter().map(String::from).collect()),
        ..Default::default()
    };
    let call_with = func(
        vec![Ty::Unit, Ty::Unit],
        0,
        vec![
            blk(
                0,
                vec![],
                call(
                    vec![Operand::Constant(ConstValue::opaque_const())],
                    Place::local(1),
                    Some(1),
                    None,
                ),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    );
    // No evidence (no facts, or `None`): refused, as before.
    assert!(matches!(
        obligation_points(&call_with, None, &inp),
        Err(TinvObligationRefusal::Write(_))
    ));
    assert!(matches!(
        obligation_points(&call_with, Some(&with(None, 2)), &inp),
        Err(TinvObligationRefusal::Write(_))
    ));
    // Evidence that a constant of the body may hold THIS type: refused.
    assert!(matches!(
        obligation_points(&call_with, Some(&with(Some(vec![name.as_str()]), 2)), &inp),
        Err(TinvObligationRefusal::Write(_))
    ));
    // Evidence that no constant can hold it (another type's constants only): cleared.
    assert!(obligation_points(&call_with, Some(&with(Some(vec!["c::Other"]), 2)), &inp).is_ok());
    // A constant stored into an S-typed local contradicts the evidence: still refused.
    let store = func(
        vec![Ty::Unit, s_ty()],
        0,
        vec![blk(
            0,
            vec![assign(
                Place::local(1),
                Rvalue::Use(Operand::Constant(ConstValue::opaque_const())),
            )],
            Terminator::Return,
        )],
    );
    assert!(matches!(
        obligation_points(&store, Some(&with(Some(vec![]), 1)), &inp),
        Err(TinvObligationRefusal::Write(_))
    ));
}

/// Decision TINV-33: the census's crate-level `dyn`/parameter evidence reaches the mint
/// through the body's facts, per type, and never past a value that does reach `S`.
#[test]
fn opaque_evidence_admits_a_dyn_call_argument_at_the_mint() {
    let ty = tinv();
    let name = ty.def_path.clone();
    let inventory: HashSet<CalleeIdentity> = [ident(INV)].into_iter().collect();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    let dyn_write = Ty::Dynamic { trait_name: "core::fmt::Write".into(), principal_key: None };
    let formatter = adt("core::fmt::Formatter", vec![("buf", mut_ref(dyn_write))]);
    let param = Ty::Unsupported { kind: "TyKind::Param".into(), detail: "R".into() };
    let call_on = |arg_ty: Ty| {
        func(
            vec![Ty::Unit, arg_ty, Ty::Unit],
            1,
            vec![
                blk(
                    0,
                    vec![],
                    call(vec![Operand::Move(Place::local(1))], Place::local(2), Some(1), None),
                ),
                blk(1, vec![], Terminator::Return),
            ],
        )
    };
    let facts = |dyn_names: Vec<&str>, param_names: Vec<&str>| TinvBodyFacts {
        block_count: 2,
        dyn_unreachable: dyn_names.into_iter().map(String::from).collect(),
        param_unreachable: param_names.into_iter().map(String::from).collect(),
        ..Default::default()
    };
    let fmt_body = call_on(mut_ref(formatter));
    let param_body = call_on(mut_ref(param));
    // No evidence (no facts, or evidence for another type): refused, as before.
    for f in [&fmt_body, &param_body] {
        assert!(matches!(obligation_points(f, None, &inp), Err(TinvObligationRefusal::Write(_))));
        assert!(matches!(
            obligation_points(f, Some(&facts(vec!["c::Other"], vec!["c::Other"])), &inp),
            Err(TinvObligationRefusal::Write(_))
        ));
    }
    // `dyn` evidence admits the Formatter argument but not the parameter.
    assert!(obligation_points(&fmt_body, Some(&facts(vec![name.as_str()], vec![])), &inp).is_ok());
    assert!(matches!(
        obligation_points(&param_body, Some(&facts(vec![name.as_str()], vec![])), &inp),
        Err(TinvObligationRefusal::Write(_))
    ));
    // Parameter evidence counts only together with the `dyn` evidence.
    assert!(matches!(
        obligation_points(&param_body, Some(&facts(vec![], vec![name.as_str()])), &inp),
        Err(TinvObligationRefusal::Write(_))
    ));
    assert!(
        obligation_points(
            &param_body,
            Some(&facts(vec![name.as_str()], vec![name.as_str()])),
            &inp
        )
        .is_ok()
    );
    // An argument that really reaches `S` beside the `dyn` is still a root, not cleared.
    let with_s = call_on(Ty::Tuple(vec![
        mut_ref(Ty::Dynamic { trait_name: "t::Tr".into(), principal_key: None }),
        mut_ref(s_ty()),
    ]));
    let r =
        obligation_points(&with_s, Some(&facts(vec![name.as_str()], vec![name.as_str()])), &inp);
    assert!(!matches!(r, Ok(ref rows) if rows.is_empty()), "{r:?}");
}

/// TINV-32 minors: at the mint, the evidence never clears a scalar-field struct constant
/// of `S`, nor an `OpaqueConst` that is a whole assignment rvalue (the extractor invents
/// those for non-constant rvalues such as a `Box<dyn Trait>` unsize).
#[test]
fn constant_evidence_never_clears_an_s_struct_or_an_invented_opaque() {
    let ty = tinv();
    let inventory: HashSet<CalleeIdentity> = [ident(INV)].into_iter().collect();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    let cleared = |blocks: usize| TinvBodyFacts {
        block_count: blocks,
        constants_may_hold: Some(Default::default()),
        ..Default::default()
    };
    let s_struct = func(
        vec![Ty::Unit, Ty::Unit],
        0,
        vec![
            blk(
                0,
                vec![],
                call(
                    vec![Operand::Constant(ConstValue::struct_scalar_fields_ref("c::S", vec![]))],
                    Place::local(1),
                    Some(1),
                    None,
                ),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    );
    assert!(matches!(
        obligation_points(&s_struct, Some(&cleared(2)), &inp),
        Err(TinvObligationRefusal::Write(_))
    ));
    let dyn_box = Ty::Unsupported { kind: "TyKind::Alias".into(), detail: "opaque".into() };
    let invented = func(
        vec![Ty::Unit, dyn_box],
        0,
        vec![blk(
            0,
            vec![assign(
                Place::local(1),
                Rvalue::Use(Operand::Constant(ConstValue::opaque_const())),
            )],
            Terminator::Return,
        )],
    );
    assert!(matches!(
        obligation_points(&invented, Some(&cleared(1)), &inp),
        Err(TinvObligationRefusal::Write(_))
    ));
}
