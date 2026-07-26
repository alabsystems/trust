use trust_types::UnwindEdge;
use trust_types::{
    AggregateKind, BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VariantDef, VcKind,
    VerifiableBody, VerifiableFunction,
};

use super::{
    generate_unwrap_panic_freedom_vcs, unsupported_mir_vcs, v2_build_path_definition_map,
};

const RESULT_UNWRAP: &str = "core::result::Result::<T, E>::unwrap";
const OPTION_EXPECT: &str = "core::option::Option::<T>::expect";

fn enter_bool_pred_summaries(
    summaries: trust_types::fx::FxHashMap<String, super::ReturnBoolPredSummary>,
) -> crate::VcgenContextGuard {
    crate::enter_test_callee_summaries(
        crate::CalleeSummaryContext::default().with_return_bool_preds(summaries),
    )
}

/// `Result<u64, ()>` in the flattened `lower_enum_adt` shape: the explicit
/// `__tag` slot plus per-variant defs carrying the REAL discriminant tags.
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

/// `Option<u64>` in the same flattened shape (`None` = 0, `Some` = 1).
fn std_option_ty() -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
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
        faithful_enum_repr: None, enum_layout: None, }
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
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "unwrap_fixture".into(),
        def_path: "test::unwrap_fixture".into(),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count, return_ty: Ty::u64() },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `fn f(r: Result<u64, ()>) { let d = discr(r); if d == 0 { r.unwrap() } }`
///   bb0: d = Discriminant(r); SwitchInt(d) -> [0: bb1], otherwise: bb2
///   bb1: x = Result::unwrap(move r) -> bb3
fn guarded_result_unwrap_fn() -> VerifiableFunction {
    func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_result_ty(), name: Some("r".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::Int { width: 64, signed: true },
                name: Some("d".into()),
            },
            LocalDecl { index: 3, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
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
                stmts: vec![],
                terminator: call_term(
                    RESULT_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    3,
                    3,
                ),
            },
            ret_block(2),
            ret_block(3),
        ],
        1,
    )
}

/// Count `Call::…::panic-freedom-unverified` UnsupportedMir rows.
fn unverified_row_count(func: &VerifiableFunction) -> usize {
    unsupported_mir_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind.ends_with("::panic-freedom-unverified"))
        })
        .count()
}

/// `pred` holds for some AND-reachable conjunct of `f` (never descends into
/// `Or` — so a disjunctive fact like the variant-range `d ∈ {0,1}` cannot
/// satisfy an `Eq` conjunct probe).
fn has_and_conjunct(f: &Formula, pred: &dyn Fn(&Formula) -> bool) -> bool {
    if pred(f) {
        return true;
    }
    match f {
        Formula::And(cs) => cs.iter().any(|c| has_and_conjunct(c, pred)),
        _ => false,
    }
}

fn eq_var_int(f: &Formula, name: &str, value: i128) -> bool {
    matches!(f, Formula::Eq(l, r)
        if matches!(l.as_ref(), Formula::Var(n, _) if n.split('#').next() == Some(name))
            && matches!(r.as_ref(), Formula::Int(v) if *v == value))
}

fn eq_int_int(f: &Formula, a: i128, b: i128) -> bool {
    matches!(f, Formula::Eq(l, r)
        if matches!(l.as_ref(), Formula::Int(v) if *v == a)
            && matches!(r.as_ref(), Formula::Int(v) if *v == b))
}

/// (1) Guard-pinned unwrap: the VC exists, is UNSAT-SHAPED — the body pins
/// the receiver tag to the PANIC tag (`d == 1`, Err) while the dominating
/// switch guard pins the success tag (`d == 0`) — and the fail-closed
/// UnsupportedMir row is REPLACED (0 rows), never doubled.
#[test]
fn guarded_result_unwrap_gets_unsat_shaped_vc_and_no_unsupported_row() {
    let func = guarded_result_unwrap_fn();
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1, "exactly one panic-freedom VC for the one unwrap");
    let vc = &vcs[0];
    assert!(
        matches!(&vc.kind, VcKind::Assertion { message } if message == "Call::unwrap::panic-freedom"),
        "kind must be the panic-freedom assertion; got {:?}",
        vc.kind
    );
    assert!(
        has_and_conjunct(&vc.formula, &|f| eq_var_int(f, "d", 1)),
        "the body must assert the PANIC (Err) tag `d == 1`: {:?}",
        vc.formula
    );
    assert!(
        has_and_conjunct(&vc.formula, &|f| eq_var_int(f, "d", 0)),
        "the dominating guard `d == 0` must be conjoined (UNSAT shape): {:?}",
        vc.formula
    );
    assert_eq!(unverified_row_count(&func), 0, "the UnsupportedMir row must be replaced");
}

/// (2a) Unguarded unwrap WITH a discriminant read: the VC stays REFUTABLE —
/// the body `d == 1` is present but NO success-guard conjunct pins `d` — so
/// the solver can reach SAT (may panic) and the row stays failed, never proved.
#[test]
fn unguarded_unwrap_with_read_is_refutable_not_guard_pinned() {
    let mut func = guarded_result_unwrap_fn();
    // Collapse the guard: bb0 calls unwrap directly after the read.
    func.body.blocks[0].terminator =
        call_term(RESULT_UNWRAP, vec![Operand::Move(Place::local(1))], 3, 1);
    func.body.blocks.truncate(2);
    func.body.blocks[1] = ret_block(1);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "d", 1)),
        "the refutation body `d == 1` must be present: {:?}",
        vcs[0].formula
    );
    assert!(
        !has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "d", 0)),
        "no success-pin conjunct may appear on the unguarded path: {:?}",
        vcs[0].formula
    );
    assert_eq!(unverified_row_count(&func), 0);
}

/// (2b) Unguarded PARAM unwrap with NO pinning read, no construction, and no
/// other tag observer: shape (d) fires — the receiver's tag is a FREE entry
/// value, so a solvable REFUTATION VC (`r.__tag == Err`) replaces the
/// fail-closed UnsupportedMir row. SAT with `r.0 = 1` is a GENUINE `Err`
/// argument reaching the unwrap (a real counterexample), not a coverage gap.
/// (Pre-shape-(d) this expected the fail-closed row; the row is now the
/// fallback only for shapes with an unconnected observer — see (2c).)
#[test]
fn param_unwrap_refutes_with_free_entry_tag() {
    let mut func = guarded_result_unwrap_fn();
    func.body.blocks[0].stmts.clear(); // drop the discriminant read
    func.body.blocks[0].terminator =
        call_term(RESULT_UNWRAP, vec![Operand::Move(Place::local(1))], 3, 1);
    func.body.blocks.truncate(2);
    func.body.blocks[1] = ret_block(1);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1, "shape (d) must mint one refutation VC");
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "r.0", 1)),
        "the body must pin the FREE entry tag to the PANIC (Err) tag: {:?}",
        vcs[0].formula
    );
    assert!(
        !has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "r.0", 0)),
        "no success-pin conjunct may appear (the VC must stay SAT/refutable): {:?}",
        vcs[0].formula
    );
    assert_eq!(unverified_row_count(&func), 0, "the fail-closed row is replaced");
}

/// (2d) Un-inlined `is_some()` guard: `_b = &o; g = is_some(_b); if g {
/// o.unwrap() }`. The probe model records `(g ∧ o.__tag == Some) ∨ (¬g ∧
/// o.__tag ≠ Some)` as a path definition over the SHARED entry-tag
/// variable, the modeled probe is whitelisted as a CONNECTED observer, and
/// shape (d) still mints the refutation VC — the solver then has guard `g`
/// (path guard) ∧ probe semantics ∧ body `o.0 == None` ⇒ UNSAT ⇒ PROVED.
#[test]
fn param_unwrap_guarded_by_uninlined_is_some_connects() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: Ty::Unit, name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 4, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_IS_SOME,
                    vec![Operand::Move(Place::local(2))],
                    3,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(3)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    4,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    // Shape (d) mints the refutation VC (the modeled probe is CONNECTED, so
    // the observer gate does not fail closed).
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1, "modeled probe must be whitelisted; shape (d) must fire");
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "o.0", 0)),
        "the body must test the SHARED entry tag against None: {:?}",
        vcs[0].formula
    );
    assert_eq!(unverified_row_count(&func), 0, "the fail-closed row is replaced");
    // The probe's result semantics reach the unwrap block as a path
    // definition citing the SAME tag variable — the guard-connection witness.
    let defs = v2_build_path_definition_map(&func);
    let at_unwrap = format!("{:?}", defs.get(&BlockId(2)).cloned().unwrap_or_default());
    assert!(
        at_unwrap.contains("\"o.0\""),
        "probe semantics over the shared tag must reach the unwrap block: {at_unwrap}"
    );
    assert!(
        at_unwrap.contains("\"g\""),
        "the guard bool must appear in the threaded semantics: {at_unwrap}"
    );
}

/// (2h) INFERRED CONTRACT, inference side: the `my_check` probe body —
/// `fn my_check(o: &Option<u64>) -> bool { o.is_some() }` — summarizes to
/// `ret ⇔ tag(*o) == Some(=1)`; a `&mut` param records nothing.
#[test]
fn infers_bool_pred_from_probe_body() {
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    let helper = |mutable: bool| {
        func_of(
            vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable, inner: Box::new(std_option_ty()) },
                    name: Some("o".into()),
                },
                LocalDecl { index: 2, ty: Ty::Unit, name: Some("b".into()) },
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref {
                            mutable: false,
                            place: Place { local: 1, projections: vec![Projection::Deref] },
                        },
                        span: SourceSpan::default(),
                    }],
                    terminator: call_term(
                        OPTION_IS_SOME,
                        vec![Operand::Move(Place::local(2))],
                        0,
                        1,
                    ),
                },
                ret_block(1),
            ],
            1,
        )
    };
    let summaries = super::compute_return_bool_pred_summaries(&[helper(false)]);
    let s = summaries.values().next().expect("shared-ref probe body must summarize");
    assert_eq!(
        (s.enum_name.as_str(), s.pred_param, s.pred_tag, s.pred_is_eq),
        ("core::option::Option", 1, 1, true),
        "ret ⇔ tag(*o) == Some"
    );
    assert!(
        super::compute_return_bool_pred_summaries(&[helper(true)]).is_empty(),
        "a &mut param must record nothing (fail-closed)"
    );
}

/// (2h′) INFERRED CONTRACT, real-MIR receiver/hygiene shapes: the summary
/// must survive the forms rustc actually emits — the probe receiver passed
/// DIRECTLY (`is_some(copy _1)`) or through a bare copy-hop (`_t = copy _1;
/// is_some(copy _t)`), the probe result flowing through a temp, and
/// `StorageLive`/`StorageDead` annotations interleaved in every block. A
/// Tier-2a discriminant-switch body with the same storage noise infers too.
/// (Regression: the earlier reborrow-only fixture missed all three, so the
/// inference silently no-op'd on real callees.)
#[test]
fn infers_bool_pred_real_mir_shapes() {
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    let ref_option = || Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) };

    // Tier 1, direct-pass: bb0 `StorageLive(2); _2 = is_some(copy _1) -> bb1`;
    // bb1 `_0 = copy _2; StorageDead(2); return`.
    let direct = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: ref_option(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("b".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::StorageLive(2)],
                terminator: call_term(
                    OPTION_IS_SOME,
                    vec![Operand::Copy(Place::local(1))],
                    2,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    },
                    Statement::StorageDead(2),
                ],
                terminator: Terminator::Return,
            },
        ],
        1,
    );

    // Tier 1, copy-hop: bb0 `StorageLive(2); _2 = copy _1; StorageLive(3);
    // _3 = is_some(copy _2) -> bb1`; bb1 `_0 = copy _3; return`.
    let copy_hop = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: ref_option(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: ref_option(), name: Some("p".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("b".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::StorageLive(2),
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                    Statement::StorageLive(3),
                ],
                terminator: call_term(
                    OPTION_IS_SOME,
                    vec![Operand::Copy(Place::local(2))],
                    3,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ],
        1,
    );

    for (label, f) in [("direct-pass", direct), ("copy-hop", copy_hop)] {
        let summaries = super::compute_return_bool_pred_summaries(&[f]);
        let s = summaries
            .values()
            .next()
            .unwrap_or_else(|| panic!("{label} probe body must summarize"));
        assert_eq!(
            (s.enum_name.as_str(), s.pred_param, s.pred_tag, s.pred_is_eq),
            ("core::option::Option", 1, 1, true),
            "{label}: ret ⇔ tag(*o) == Some",
        );
    }

    // Tier 2a with storage noise: `match *o { None => true, Some => false }`
    // → `ret ⇔ tag(*o) == None(=0)`. bb0 `StorageLive(2); _2 = discr(*_1);
    // switch`; each arm `StorageDead(2); _0 = const; goto bb3`; bb3 returns.
    let bool_const = |b: bool| Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(b)));
    let switch_body = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: ref_option(), name: Some("o".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::Int { width: 64, signed: true },
                name: Some("d".into()),
            },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::StorageLive(2),
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Discriminant(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        }),
                        span: SourceSpan::default(),
                    },
                ],
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
                stmts: vec![
                    Statement::StorageDead(2),
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: bool_const(true),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![
                    Statement::StorageDead(2),
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: bool_const(false),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Goto(BlockId(3)),
            },
            ret_block(3),
        ],
        1,
    );
    let summaries = super::compute_return_bool_pred_summaries(&[switch_body]);
    let s = summaries.values().next().expect("switch body must summarize");
    assert_eq!(
        (s.enum_name.as_str(), s.pred_param, s.pred_tag, s.pred_is_eq),
        ("core::option::Option", 1, 0, true),
        "ret ⇔ tag(*o) == None",
    );
}

/// (2j) TIER 2b — a probe result feeding a Bool switch:
/// `fn f(o: &Option<u64>) -> bool { if o.is_some() { A } else { B } }`.
/// (A=true,B=false) is `is_some` (`ret ⇔ tag == Some`); (A=false,B=true) is
/// the negation `is_none` (`ret ⇔ tag == None`); (A==B) is a constant and
/// records nothing (fail-closed). The switch discriminant is the probe
/// result, so value-`0` is the probe-false arm.
#[test]
fn infers_bool_pred_from_probe_fed_switch() {
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    // bb0: _2 = &(*_1); _3 = is_some(move _2) -> bb1
    // bb1: switchInt(_3) -> [0: bb2 (probe false)], otherwise: bb3 (probe true)
    // bb2: _0 = v_false; goto bb4   bb3: _0 = v_true; goto bb4   bb4: return
    let build = |v_true: bool, v_false: bool| {
        let ref_option = || Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) };
        func_of(
            vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: ref_option(), name: Some("o".into()) },
                LocalDecl { index: 2, ty: ref_option(), name: Some("r".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("p".into()) },
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::StorageLive(2),
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Ref {
                                mutable: false,
                                place: Place { local: 1, projections: vec![Projection::Deref] },
                            },
                            span: SourceSpan::default(),
                        },
                        Statement::StorageLive(3),
                    ],
                    terminator: call_term(
                        OPTION_IS_SOME,
                        vec![Operand::Move(Place::local(2))],
                        3,
                        1,
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(
                            v_false,
                        ))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(
                            v_true,
                        ))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                ret_block(4),
            ],
            1,
        )
    };
    // (true, false) => is_some => ret ⇔ tag == Some(=1).
    let a = super::compute_return_bool_pred_summaries(&[build(true, false)]);
    let a = a.values().next().expect("is_some-long must summarize");
    assert_eq!(
        (a.enum_name.as_str(), a.pred_param, a.pred_tag, a.pred_is_eq),
        ("core::option::Option", 1, 1, true),
        "if is_some {{ true }} else {{ false }} == tag Some",
    );
    // (false, true) => negation => is_none => ret ⇔ tag == None(=0).
    let b = super::compute_return_bool_pred_summaries(&[build(false, true)]);
    let b = b.values().next().expect("is_none-long must summarize");
    assert_eq!(
        (b.enum_name.as_str(), b.pred_param, b.pred_tag, b.pred_is_eq),
        ("core::option::Option", 1, 0, true),
        "if is_some {{ false }} else {{ true }} == tag None",
    );
    // (true, true) => constant => records nothing (fail-closed).
    assert!(
        super::compute_return_bool_pred_summaries(&[build(true, true)]).is_empty(),
        "a constant-return body is not a predicate"
    );
}

/// (2k) FIELD SUBJECT — `fn is_ready(&self) -> bool { self.slot.is_some() }`.
/// The `&Struct` param's probed field (index 0, `Option<u64>`) yields a
/// summary with `pred_field = Some(0)`; the tag term is minted over the
/// projected place `(*self).0`. A `&mut Struct` param records nothing
/// (fail-closed — the field could be mutated between guard and unwrap).
#[test]
fn infers_bool_pred_from_field_probe() {
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    let widget_ref = |mutable: bool| Ty::Ref {
        mutable,
        inner: Box::new(Ty::Adt { adt_kind: None, layout: None, 
            name: "mycrate::Widget".into(),
            fields: vec![("slot".into(), std_option_ty())],
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, }),
    };
    // bb0: _2 = &((*_1).0); _3 = is_some(move _2) -> bb1
    // bb1: _0 = copy _3; return
    let helper = |mutable: bool| {
        func_of(
            vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: widget_ref(mutable), name: Some("self".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) },
                    name: Some("r".into()),
                },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("b".into()) },
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::StorageLive(2),
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Ref {
                                mutable: false,
                                place: Place {
                                    local: 1,
                                    projections: vec![Projection::Deref, Projection::Field(0)],
                                },
                            },
                            span: SourceSpan::default(),
                        },
                        Statement::StorageLive(3),
                    ],
                    terminator: call_term(
                        OPTION_IS_SOME,
                        vec![Operand::Move(Place::local(2))],
                        3,
                        1,
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            1,
        )
    };
    let s = super::compute_return_bool_pred_summaries(&[helper(false)]);
    let s = s.values().next().expect("field probe body must summarize");
    assert_eq!(
        (s.enum_name.as_str(), s.pred_param, s.pred_field, s.pred_tag, s.pred_is_eq),
        ("core::option::Option", 1, Some(0), 1, true),
        "ret ⇔ tag((*self).slot) == Some",
    );
    assert!(
        super::compute_return_bool_pred_summaries(&[helper(true)]).is_empty(),
        "a &mut Struct param must record nothing (fail-closed)"
    );
}

/// (2i) INFERRED CONTRACT, consumer side: `if my_check(&o) { o.unwrap() }`
/// with the inferred summary installed — the helper call is a CONNECTED
/// observer, shape (d) fires, and the contract's probe-shaped facts reach
/// the unwrap block over the SHARED tag term. Without the summary the same
/// fixture stays fail-closed.
#[test]
fn helper_guarded_unwrap_connects_via_inferred_contract() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const HELPER: &str = "corpus::my_check";
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: Ty::Unit, name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 4, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(HELPER, vec![Operand::Move(Place::local(2))], 3, 1),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(3)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    4,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    // WITHOUT the summary: opaque observer, fail-closed row.
    assert!(generate_unwrap_panic_freedom_vcs(&func).is_empty());
    assert_eq!(unverified_row_count(&func), 1);
    // WITH the inferred contract: connected, shape (d) fires.
    let mut map = trust_types::fx::FxHashMap::default();
    map.insert(
        HELPER.to_string(),
        super::ReturnBoolPredSummary {
            enum_name: "core::option::Option".into(),
            params: vec!["o".into()],
            pred_param: 1,
            pred_field: None,
            kind: super::ReturnBoolPredKind::Iff,
            pred_tag: 1,
            pred_is_eq: true,
            variants: vec![0, 1],
        },
    );
    let _summary_scope = enter_bool_pred_summaries(map);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    let defs = v2_build_path_definition_map(&func);
    let at_unwrap = format!("{:?}", defs.get(&BlockId(2)).cloned().unwrap_or_default());
    let rows_with_summary = unverified_row_count(&func);
    assert_eq!(vcs.len(), 1, "summarized helper must be a connected observer");
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "o.0", 0)),
        "the body must test the SHARED entry tag against None: {:?}",
        vcs[0].formula
    );
    assert_eq!(rows_with_summary, 0, "the fail-closed row is replaced");
    assert!(
        at_unwrap.contains("\"o.0\"") && at_unwrap.contains("\"g\""),
        "the inferred contract's facts must reach the unwrap block: {at_unwrap}"
    );
}

/// (2l) FIELD guard, consumer side + unwrap field path end to end:
/// `fn use_it(x: &Widget) { if x.is_ready() { x.slot.unwrap() } }`. Without
/// the summary the guard is an OPAQUE observer of the base and the field
/// unwrap keeps its fail-closed row. WITH the field contract
/// (`pred_field = Some(0)`) the guard is a CONNECTED field observer, the
/// field unwrap's shape-(d) refutation fires over the SHARED field tag term
/// `x*.0.0`, and the contract's facts reach the unwrap block — so a
/// dominating field guard proves the field unwrap.
#[test]
fn field_guarded_field_unwrap_connects_via_inferred_contract() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const IS_READY: &str = "mycrate::Widget::is_ready";
    let widget_ref = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Adt { adt_kind: None, layout: None, 
            name: "mycrate::Widget".into(),
            fields: vec![("slot".into(), std_option_ty())],
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, }),
    };
    // bb0: _2 = is_ready(copy _1) -> bb1
    // bb1: switchInt(_2) -> [0: bb3], otherwise: bb2   (guard TRUE → unwrap)
    // bb2: _3 = copy ((*_1).0); _4 = Option::unwrap(move _3) -> bb4
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: widget_ref, name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 3, ty: std_option_ty(), name: Some("t".into()) },
            LocalDecl { index: 4, ty: Ty::u64(), name: Some("v".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: call_term(IS_READY, vec![Operand::Copy(Place::local(1))], 2, 1),
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
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Field(0)],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(3))],
                    4,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    // WITHOUT the summary: the guard borrows the base → opaque observer →
    // the field unwrap keeps its fail-closed row.
    assert!(generate_unwrap_panic_freedom_vcs(&func).is_empty());
    assert_eq!(unverified_row_count(&func), 1);
    // WITH the field contract: connected field observer, shape (d) fires.
    let mut map = trust_types::fx::FxHashMap::default();
    map.insert(
        IS_READY.to_string(),
        super::ReturnBoolPredSummary {
            enum_name: "core::option::Option".into(),
            params: vec!["self".into()],
            pred_param: 1,
            pred_field: Some(0),
            kind: super::ReturnBoolPredKind::Iff,
            pred_tag: 1,
            pred_is_eq: true,
            variants: vec![0, 1],
        },
    );
    let _summary_scope = enter_bool_pred_summaries(map);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    let defs = v2_build_path_definition_map(&func);
    let at_unwrap = format!("{:?}", defs.get(&BlockId(2)).cloned().unwrap_or_default());
    let rows_with_summary = unverified_row_count(&func);
    assert_eq!(vcs.len(), 1, "summarized field guard must connect the field unwrap");
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "x*.0.0", 0)),
        "the body must test the SHARED field tag against None: {:?}",
        vcs[0].formula
    );
    assert_eq!(rows_with_summary, 0, "the fail-closed field row is replaced");
    assert!(
        at_unwrap.contains("\"x*.0.0\"") && at_unwrap.contains("\"g\""),
        "the field contract's facts must reach the unwrap block: {at_unwrap}"
    );
}

/// (2m) UNGUARDED field unwrap REFUTES: `fn use_it(x: &Widget) ->
/// { x.slot.unwrap() }`. With no observer of the field, its tag is a FREE
/// entry value — shape (d) mints the refutation `x*.0.0 == None(=0)` (SAT ⇒ a
/// genuine `x.slot == None` witness reaching the unwrap), NOT a fail-closed
/// row. The soundness complement of the guarded case.
#[test]
fn unguarded_field_unwrap_refutes_with_witness() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Ref {
                    mutable: false,
                    inner: Box::new(Ty::Adt { adt_kind: None, layout: None, 
                        name: "mycrate::Widget".into(),
                        fields: vec![("slot".into(), std_option_ty())],
                        variants: vec![],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, }),
                },
                name: Some("x".into()),
            },
            LocalDecl { index: 2, ty: std_option_ty(), name: Some("t".into()) },
            LocalDecl { index: 3, ty: Ty::u64(), name: Some("v".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Field(0)],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(2))],
                    3,
                    1,
                ),
            },
            ret_block(1),
        ],
        1,
    );
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1, "an unguarded field unwrap must refute, not fail closed");
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "x*.0.0", 0)),
        "refutation must test the free field tag against None: {:?}",
        vcs[0].formula
    );
    assert_eq!(unverified_row_count(&func), 0, "no fail-closed row when it refutes");
}

/// SOUNDNESS regression (audit finding, critical): a helper whose probe is
/// NOT the sole determinant of `_0` — `fn h(o:&Option<u64>)->bool{ flag ||
/// o.is_some() }` — must NOT summarize. The probe sits in a NON-entry block
/// behind a bypass arm (`_0 = true`); before the entry-block gate, the
/// recognizer walked only the probe's forward path and recorded the FALSE
/// contract `ret ⇔ tag==Some` (a caller `if h(&o){o.unwrap()}` then
/// FALSE-PROVED although `h` is true for `flag` regardless of the tag).
#[test]
fn multi_arm_probe_body_records_nothing() {
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    // bb0: switchInt(flag) -> [0: bb1], otherwise: bb2   (probe NOT at entry)
    // bb1: _3 = &(*_1); _4 = is_some(move _3) -> bb3
    // bb2: _0 = true; goto bb4     bb3: _0 = move _4; goto bb4   bb4: return
    let helper = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) },
                name: Some("o".into()),
            },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) },
                name: Some("r".into()),
            },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("b".into()) },
        ],
        vec![
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
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_IS_SOME,
                    vec![Operand::Move(Place::local(3))],
                    4,
                    3,
                ),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(true))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(4)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::local(4))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(4)),
            },
            ret_block(4),
        ],
        1,
    );
    assert!(
        super::compute_return_bool_pred_summaries(&[helper]).is_empty(),
        "a probe behind a bypass arm must NOT summarize (false-PROVE hole)"
    );
}

/// SOUNDNESS regression (audit finding, critical): `place_to_var_name`'s
/// `_<L>` fallback must never collide with a DIFFERENT local's source name
/// literally spelled `_<L>`. Here local 1 is unnamed (fallback `_1`) and
/// local 2 is source-named `_1`; distinct locals must mint distinct vars, or
/// a fact keyed to one silently discharges the other's obligation.
#[test]
fn place_to_var_name_fallback_never_collides() {
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: Ty::u64(), name: None },
            LocalDecl { index: 2, ty: Ty::u64(), name: Some("_1".into()) },
        ],
        vec![ret_block(0)],
        0,
    );
    let v1 = crate::place_to_var_name(&func, &Place::local(1));
    let v2 = crate::place_to_var_name(&func, &Place::local(2));
    assert_eq!(v1, "_1", "the unnamed local keeps its fallback");
    assert_eq!(v2, "_2", "a source name shaped like a foreign fallback is demoted");
    assert_ne!(v1, v2, "distinct locals must never share a var name");
}

/// Public Trust IR is constructible without going through the compiler
/// bridge.  A reordered/sparse declaration vector must not make local `i`
/// inherit the name stored at vector position `i`; malformed proof entry
/// points reject the body, while this public helper remains total and
/// identifies declarations by their explicit local index.
#[test]
fn place_to_var_name_sparse_table_never_uses_positional_decl() {
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 2, ty: Ty::u64(), name: Some("two".into()) },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("one".into()) },
        ],
        vec![ret_block(0)],
        0,
    );

    assert_eq!(crate::place_to_var_name(&func, &Place::local(1)), "one");
    assert_eq!(crate::place_to_var_name(&func, &Place::local(2)), "two");
    assert_eq!(crate::place_to_var_name(&func, &Place::local(7)), "_7");
}

/// A source identifier shaped like any possible fallback is reserved even
/// when that local is outside the current declaration-table length.  This
/// keeps the total public helper injective for malformed/standalone Places.
#[test]
fn place_to_var_name_reserves_all_numeric_fallbacks() {
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("_999".into()) },
        ],
        vec![ret_block(0)],
        0,
    );

    assert_eq!(crate::place_to_var_name(&func, &Place::local(1)), "_1");
    assert_eq!(crate::place_to_var_name(&func, &Place::local(999)), "_999");
}

/// SOUNDNESS regression: source identifiers may legally occupy Trust's
/// generated Formula namespace.  A scalar `s__slice_len` must not alias the
/// canonical length of a distinct slice `s`, and a scalar named exactly
/// like a const-generic symbol must not alias that const parameter.  Both
/// source locals are demoted to their injective MIR fallback names.
#[test]
fn place_to_var_name_generated_namespace_never_collides() {
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Ref {
                    mutable: false,
                    inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                },
                name: Some("s".into()),
            },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("s__slice_len".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::usize(),
                name: Some("__trust_constparam_0_N".into()),
            },
        ],
        vec![ret_block(0)],
        3,
    );

    let slice = crate::place_to_var_name(&func, &Place::local(1));
    let scalar_len = crate::place_to_var_name(&func, &Place::local(2));
    let scalar_const = crate::place_to_var_name(&func, &Place::local(3));
    assert_eq!(slice, "s");
    assert_eq!(scalar_len, "_2");
    assert_eq!(scalar_const, "_3");
    assert_ne!(scalar_len, format!("{slice}__slice_len"));
    assert_ne!(scalar_const, trust_types::const_param_symbol(0, "N"));
}

/// PRECISION regression (audit finding, low): the field observer gate must
/// follow MULTI-HOP copy aliases of the base, like the whole-local twin.
/// `fn f(x:&Foo) { let a=x; let b=a; if observe(b) { x.slot.unwrap() } }` —
/// `observe` (opaque) receives a 2-hop copy `_3=copy _2; _2=copy _1` of the
/// base. A one-hop `touches_base` misses it and spuriously refutes a
/// possibly-guarded field unwrap; the multi-hop gate keeps it fail-closed.
#[test]
fn field_observer_gate_follows_multihop_base_copy() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const OBSERVE: &str = "mycrate::observe"; // opaque, no summary
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Ref {
                    mutable: false,
                    inner: Box::new(Ty::Adt { adt_kind: None, layout: None, 
                        name: "mycrate::Foo".into(),
                        fields: vec![("slot".into(), std_option_ty())],
                        variants: vec![],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, }),
                },
                name: Some("x".into()),
            },
            LocalDecl {
                index: 2,
                ty: Ty::Ref {
                    mutable: false,
                    inner: Box::new(Ty::Adt { adt_kind: None, layout: None, 
                        name: "mycrate::Foo".into(),
                        fields: vec![("slot".into(), std_option_ty())],
                        variants: vec![],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, }),
                },
                name: Some("a".into()),
            },
            LocalDecl {
                index: 3,
                ty: Ty::Ref {
                    mutable: false,
                    inner: Box::new(Ty::Adt { adt_kind: None, layout: None, 
                        name: "mycrate::Foo".into(),
                        fields: vec![("slot".into(), std_option_ty())],
                        variants: vec![],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, }),
                },
                name: Some("b".into()),
            },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("d".into()) },
            LocalDecl { index: 5, ty: std_option_ty(), name: Some("rv".into()) },
            LocalDecl { index: 6, ty: Ty::u64(), name: Some("res".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: call_term(OBSERVE, vec![Operand::Move(Place::local(3))], 4, 1),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(4)),
                    targets: vec![(1, BlockId(2))],
                    otherwise: BlockId(3),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(5),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Field(0)],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(5))],
                    6,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    // The opaque `observe(b)` receives a 2-hop copy of the base; the field
    // unwrap must stay FAIL-CLOSED (no spurious refutation).
    assert!(
        generate_unwrap_panic_freedom_vcs(&func).is_empty(),
        "a multi-hop base-copy observer must suppress the field refutation"
    );
    assert_eq!(unverified_row_count(&func), 1, "the field unwrap keeps its fail-closed row");
}

/// (2n) BY-VALUE param — `fn check(o: Option<u64>) -> bool { o.is_some() }`.
/// The probe borrows the WHOLE param `&_1` (not `&(*_1)`); summarizes to the
/// same whole-pointee contract (`pred_field = None`, `ret ⇔ tag(o) == Some`).
#[test]
fn infers_bool_pred_by_value_param() {
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    let helper = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) },
                name: Some("r".into()),
            },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("b".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_IS_SOME,
                    vec![Operand::Move(Place::local(2))],
                    3,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::local(3))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ],
        1,
    );
    let s = super::compute_return_bool_pred_summaries(&[helper]);
    let s = s.values().next().expect("by-value probe body must summarize");
    assert_eq!(
        (s.enum_name.as_str(), s.pred_param, s.pred_field, s.pred_tag, s.pred_is_eq),
        ("core::option::Option", 1, None, 1, true),
        "ret ⇔ tag(o) == Some for a by-value Option param",
    );
}

/// (2p) MULTI-PARAM helper: `fn check(o: &Option<u64>, flag: bool) -> bool {
/// o.is_some() }`. The extra `flag` param is never read into `_0` (the probe
/// of `_1` dominates the Return), so `ret ⇔ tag(*o) == Some` regardless of
/// flag. Summarizes with params at FULL arity (2), pred_param=1.
#[test]
fn infers_bool_pred_multi_param() {
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    let ref_option = || Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) };
    // bb0: _3 = &(*_1); _4 = is_some(move _3) -> bb1;  bb1: _0 = move _4; ret
    let helper = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: ref_option(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
            LocalDecl { index: 3, ty: ref_option(), name: Some("r".into()) },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("b".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_IS_SOME,
                    vec![Operand::Move(Place::local(3))],
                    4,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::local(4))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ],
        2,
    );
    let s = super::compute_return_bool_pred_summaries(&[helper]);
    let s = s.values().next().expect("multi-param probe body must summarize");
    assert_eq!(
        (s.enum_name.as_str(), s.pred_param, s.pred_field, s.pred_tag, s.pred_is_eq),
        ("core::option::Option", 1, None, 1, true),
        "ret ⇔ tag(*o) == Some, independent of the extra param",
    );
    assert_eq!(s.params.len(), 2, "params recorded at full arity for the consumer arity match");
}

/// MULTI-PARAM consumer integration + negative: the inferred contract for
/// `check(&o, flag)` connects `o` only when the call-site arity exactly
/// matches the recorded helper arity. A stale summary must not partially
/// match and discharge an unwrap obligation.
#[test]
fn multi_param_consumer_connects_only_at_exact_arity() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const CHECK: &str = "corpus::check_two";
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) },
                name: Some("r".into()),
            },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 5, ty: Ty::u64(), name: Some("value".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    CHECK,
                    vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(2))],
                    4,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(4)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    5,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        2,
    );

    let summary = |arity: usize| super::ReturnBoolPredSummary {
        enum_name: "core::option::Option".into(),
        params: (0..arity).map(|index| format!("p{index}")).collect(),
        pred_param: 1,
        pred_field: None,
        kind: super::ReturnBoolPredKind::Iff,
        pred_tag: 1,
        pred_is_eq: true,
        variants: vec![0, 1],
    };

    let mut map = trust_types::fx::FxHashMap::default();
    map.insert(CHECK.to_string(), summary(2));
    let exact_scope = enter_bool_pred_summaries(map);
    let exact_vcs = generate_unwrap_panic_freedom_vcs(&func);
    let exact_rows = unverified_row_count(&func);
    assert_eq!(exact_vcs.len(), 1, "the exact two-argument call must connect the guard");
    assert_eq!(exact_rows, 0, "exact arity replaces the fail-closed observer row");
    drop(exact_scope);

    let mut stale = trust_types::fx::FxHashMap::default();
    stale.insert(CHECK.to_string(), summary(3));
    let _stale_scope = enter_bool_pred_summaries(stale);
    let mismatched_vcs = generate_unwrap_panic_freedom_vcs(&func);
    let mismatched_rows = unverified_row_count(&func);
    assert!(
        mismatched_vcs.is_empty(),
        "a wrong-arity summary must not mint predicate facts: {mismatched_vcs:?}"
    );
    assert_eq!(
        mismatched_rows, 1,
        "a wrong-arity summary leaves the observed unwrap fail-closed"
    );
}

/// (2p2) ENUM-NOT-FIRST: `fn check(flag: bool, o: &Option<u32>) -> bool {
/// o.is_some() }` — the enum is param `_2`, not `_1`. The recognizer scans
/// params and anchors the subject to `_2` (pred_param=2); the consumer
/// resolves the pred actual as `args[1]`.
#[test]
fn infers_bool_pred_enum_not_first() {
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    let ref_option = || Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) };
    // bb0: _3 = &(*_2); _4 = is_some(move _3) -> bb1;  bb1: _0 = move _4; ret
    let helper = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
            LocalDecl { index: 2, ty: ref_option(), name: Some("o".into()) },
            LocalDecl { index: 3, ty: ref_option(), name: Some("r".into()) },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("b".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 2, projections: vec![Projection::Deref] },
                    },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_IS_SOME,
                    vec![Operand::Move(Place::local(3))],
                    4,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::local(4))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ],
        2,
    );
    let s = super::compute_return_bool_pred_summaries(&[helper]);
    let s = s.values().next().expect("enum-not-first body must summarize");
    assert_eq!(
        (s.enum_name.as_str(), s.pred_param, s.pred_field, s.pred_tag),
        ("core::option::Option", 2, None, 1),
        "subject anchored to param _2 (pred_param=2)",
    );
}

/// (2q) IMPLICATION-ONLY: a payload-guarded predicate
/// `fn is_big(o: &Option<u32>) -> bool { matches!(o, Some(x) if *x > 5) }`.
/// The None arm is provably const-false; the Some arm computes `*x > 5` (a
/// NON-const). So `ret ⇒ tag == Some` (ImpliesTrue) — NOT a full iff (Some(3)
/// gives false). pred_tag = Some.
#[test]
fn infers_implies_true_from_payload_guard() {
    let helper = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) },
                name: Some("o".into()),
            },
            LocalDecl {
                index: 2,
                ty: Ty::Int { width: 64, signed: true },
                name: Some("d".into()),
            },
            LocalDecl { index: 3, ty: Ty::u64(), name: Some("x".into()) },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("c".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Discriminant(Place {
                        local: 1,
                        projections: vec![Projection::Deref],
                    }),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    // case 1 (Some) -> bb1; otherwise (None) -> bb2
                    targets: vec![(1, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    // _3 = ((*_1) as Some).0   (payload)
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![
                                Projection::Deref,
                                Projection::Downcast(1),
                                Projection::Field(0),
                            ],
                        })),
                        span: SourceSpan::default(),
                    },
                    // _4 = Gt(_3, 5)
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            trust_types::BinOp::Gt,
                            Operand::Copy(Place::local(3)),
                            Operand::Constant(trust_types::ConstValue::Uint(5, 32)),
                        ),
                        span: SourceSpan::default(),
                    },
                    // _0 = move _4   (NON-const)
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Move(Place::local(4))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(
                        false,
                    ))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(3)),
            },
            ret_block(3),
        ],
        1,
    );
    let s = super::compute_return_bool_pred_summaries(&[helper]);
    let s = s.values().next().expect("payload-guarded body must summarize as ImpliesTrue");
    assert_eq!(
        (s.enum_name.as_str(), s.pred_field, s.pred_tag, s.pred_is_eq, s.kind),
        ("core::option::Option", None, 1, true, super::ReturnBoolPredKind::ImpliesTrue),
        "ret ⇒ tag(*o) == Some (one-directional)",
    );
}

/// (2r) IMPLICATION consumer: an ImpliesTrue contract emits the WEAKER fact
/// `g ⇒ (tag==Some)` = `¬g ∨ tag==Some`, NOT the iff. On the positive guard
/// `if is_big(o) { o.unwrap() }` the g=true path guard forces tag==Some,
/// discharging the None refutation (UNSAT ⇒ PROVED). Crucially the fact does
/// NOT carry the iff's `¬g ⇒ ¬(tag==Some)` disjunct — so it can never
/// spuriously discharge the INVERSE guard's ¬g path (that VC stays SAT ⇒
/// refutable, never falsely proved). We assert the fact FORM (the solver
/// then decides prove/refute per path).
#[test]
fn implies_true_emits_one_directional_fact() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const IS_BIG: &str = "corpus::is_big";
    // if g { o.unwrap() }  (unwrap on the g=true edge)
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: Ty::Unit, name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 4, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(IS_BIG, vec![Operand::Move(Place::local(2))], 3, 1),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(3)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    4,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    let mut map = trust_types::fx::FxHashMap::default();
    map.insert(
        IS_BIG.to_string(),
        super::ReturnBoolPredSummary {
            enum_name: "core::option::Option".into(),
            params: vec!["o".into()],
            pred_param: 1,
            pred_field: None,
            kind: super::ReturnBoolPredKind::ImpliesTrue,
            pred_tag: 1,
            pred_is_eq: true,
            variants: vec![0, 1],
        },
    );
    let _summary_scope = enter_bool_pred_summaries(map);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1, "the ImpliesTrue guard connects (fact is threaded)");
    let dbg = format!("{:?}", vcs[0].formula);
    // The one-directional fact: `¬g ∨ tag==Some`.
    assert!(
        dbg.contains(r#"Or([Not(Var("g", Bool)), Eq(Var("o.0", Int), Int(1))])"#),
        "must emit the ImpliesTrue fact `¬g ∨ tag==Some`: {dbg}"
    );
    // MUST NOT emit the iff's refuting disjunct `¬g ∧ ¬(tag==Some)` — that
    // would let the inverse guard (¬g edge) spuriously prove.
    assert!(
        !dbg.contains(r#"And([Not(Var("g", Bool)), Not(Eq(Var("o.0", Int), Int(1)))])"#),
        "ImpliesTrue must NOT carry the iff's ¬g⇒¬probed clause: {dbg}"
    );
}

/// (2s) TIER2b IMPLICATION — a probe feeding an AND: `fn check(o:
/// &Option<u32>) -> bool { o.is_some() && extra }`. The probe-FALSE arm is
/// const-false; the probe-true arm computes `extra` (non-const). So `ret ⇒
/// tag == Some` (ImpliesTrue, pred_tag=Some) — the probe-fed-switch analogue
/// of the tier2a payload guard.
#[test]
fn infers_implies_true_from_probe_and() {
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    let ref_option = || Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) };
    // bb0: _2 = &(*_1); _3 = is_some(move _2) -> bb1
    // bb1: switch _3 [0: bb2 (false arm)] otherwise bb3 (true arm)
    // bb2: _0 = false; goto bb4
    // bb3: _4 = copy _3; _0 = move _4; goto bb4   (non-const true arm)
    // bb4: return
    let helper = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: ref_option(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: ref_option(), name: Some("r".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("p".into()) },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("e".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_IS_SOME,
                    vec![Operand::Move(Place::local(2))],
                    3,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(3)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(3),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(
                        false,
                    ))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(4)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![
                    // non-const: _4 = copy _3 (writes _4 first → arm is non-const)
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Move(Place::local(4))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Goto(BlockId(4)),
            },
            ret_block(4),
        ],
        1,
    );
    let s = super::compute_return_bool_pred_summaries(&[helper]);
    let s = s.values().next().expect("probe-AND body must summarize as ImpliesTrue");
    assert_eq!(
        (s.enum_name.as_str(), s.pred_field, s.pred_tag, s.kind),
        ("core::option::Option", None, 1, super::ReturnBoolPredKind::ImpliesTrue),
        "o.is_some() && extra  ⇒  ret ⇒ tag == Some",
    );
}

/// (2o) BY-VALUE guard, consumer side: `fn use_it(o: Option<u64>) { if
/// check(o) { o.unwrap() } }`. The guard actual `check(copy o)` is the enum
/// passed by value (recv IS the caller's Option local), so it connects to
/// the same origin the unwrap tests. WITH the summary shape (d) fires and
/// the fact discharges it; WITHOUT it the guard is an opaque observer of the
/// origin and the unwrap keeps its fail-closed row.
#[test]
fn by_value_guarded_unwrap_connects_via_inferred_contract() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const CHECK: &str = "corpus::check";
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 3, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: call_term(CHECK, vec![Operand::Copy(Place::local(1))], 2, 1),
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
                stmts: vec![],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    3,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    assert!(generate_unwrap_panic_freedom_vcs(&func).is_empty());
    assert_eq!(unverified_row_count(&func), 1);
    let mut map = trust_types::fx::FxHashMap::default();
    map.insert(
        CHECK.to_string(),
        super::ReturnBoolPredSummary {
            enum_name: "core::option::Option".into(),
            params: vec!["o".into()],
            pred_param: 1,
            pred_field: None,
            kind: super::ReturnBoolPredKind::Iff,
            pred_tag: 1,
            pred_is_eq: true,
            variants: vec![0, 1],
        },
    );
    let _summary_scope = enter_bool_pred_summaries(map);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    let rows = unverified_row_count(&func);
    assert_eq!(vcs.len(), 1, "a by-value guard must connect the unwrap");
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "o.0", 0)),
        "the body must test the shared entry tag against None: {:?}",
        vcs[0].formula
    );
    assert_eq!(rows, 0, "the fail-closed row is replaced");
}

/// SOUNDNESS regression (audit r4, critical, SAFE code): the WHOLE-pointee
/// consumer branch must also pin-check the guard receiver. `fn caller(o:
/// Option, o2: Option) { let mut b=&o; let m=&mut b; *m=&o2; if check(b) {
/// o.unwrap() } }` — `b` is reseated to `&o2`, so `check(b)` observes o2 not
/// o. The guard must NOT connect to `o` (which would discharge o.unwrap()
/// though o may be None); the unwrap stays fail-closed.
#[test]
fn whole_pointee_guard_through_reseat_does_not_connect() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const CHECK: &str = "corpus::check";
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: std_option_ty(), name: Some("o2".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Ref { mutable: false, inner: Box::new(std_option_ty()) },
                name: Some("b".into()),
            },
            LocalDecl {
                index: 4,
                ty: Ty::Ref {
                    mutable: true,
                    inner: Box::new(Ty::Ref {
                        mutable: false,
                        inner: Box::new(std_option_ty()),
                    }),
                },
                name: Some("m".into()),
            },
            LocalDecl { index: 5, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 6, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Ref { mutable: true, place: Place::local(3) },
                        span: SourceSpan::default(),
                    },
                    // reseat: (*m) = &o2  — rooted at _4, invisible to
                    // unique_whole_local_def(_3).
                    Statement::Assign {
                        place: Place { local: 4, projections: vec![Projection::Deref] },
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(2) },
                        span: SourceSpan::default(),
                    },
                ],
                terminator: call_term(CHECK, vec![Operand::Copy(Place::local(3))], 5, 1),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(5)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    6,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    let mut map = trust_types::fx::FxHashMap::default();
    map.insert(
        CHECK.to_string(),
        super::ReturnBoolPredSummary {
            enum_name: "core::option::Option".into(),
            params: vec!["o".into()],
            pred_param: 1,
            pred_field: None,
            kind: super::ReturnBoolPredKind::Iff,
            pred_tag: 1,
            pred_is_eq: true,
            variants: vec![0, 1],
        },
    );
    let _summary_scope = enter_bool_pred_summaries(map);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    let rows = unverified_row_count(&func);
    // The reseated guard must NOT connect o.unwrap() (that would false-PROVE);
    // it stays fail-closed.
    assert!(
        vcs.is_empty(),
        "a reseated whole-pointee guard must not connect the unwrap: {vcs:?}"
    );
    assert_eq!(rows, 1, "the unwrap stays fail-closed");
}

/// SOUNDNESS regression (audit r2, high): a field subject through a RAW
/// POINTER (or `&mut`) base must NOT be treated as pinned — the pointee can
/// be mutated via a pointer-copy alias + `SetDiscriminant` between guard and
/// unwrap (`p = copy _1; SetDiscriminant((*p).f, None)`), which the syntactic
/// pinning gate cannot see. `fn caller(p:*mut S) { if is_ready(&(*p)) {
/// (*p).f.unwrap() } }` must stay FAIL-CLOSED even with the field summary,
/// never PROVE. The shared-ref twin (`&S` base) still connects.
#[test]
fn raw_pointer_field_base_is_not_pinned() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const IS_READY: &str = "mycrate::S::is_ready";
    let s_adt = || Ty::Adt { adt_kind: None, layout: None, 
        name: "mycrate::S".into(),
        fields: vec![("f".into(), std_option_ty())],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::RawPtr { mutable: true, pointee: Box::new(s_adt()) },
                name: Some("p".into()),
            },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Ref { mutable: false, inner: Box::new(s_adt()) },
                name: Some("r".into()),
            },
            LocalDecl { index: 4, ty: std_option_ty(), name: Some("rv".into()) },
            LocalDecl { index: 5, ty: Ty::u64(), name: Some("res".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(IS_READY, vec![Operand::Move(Place::local(3))], 2, 1),
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
                    place: Place::local(4),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Field(0)],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(4))],
                    5,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    let mut map = trust_types::fx::FxHashMap::default();
    map.insert(
        IS_READY.to_string(),
        super::ReturnBoolPredSummary {
            enum_name: "core::option::Option".into(),
            params: vec!["self".into()],
            pred_param: 1,
            pred_field: Some(0),
            kind: super::ReturnBoolPredKind::Iff,
            pred_tag: 1,
            pred_is_eq: true,
            variants: vec![0, 1],
        },
    );
    let _summary_scope = enter_bool_pred_summaries(map);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    let rows = unverified_row_count(&func);
    assert!(
        vcs.is_empty(),
        "a raw-pointer field base must NOT connect / refute — it is not pinned: {vcs:?}"
    );
    assert_eq!(rows, 1, "the raw-pointer field unwrap stays fail-closed");
}

/// SOUNDNESS regression (audit r3, critical, SAFE code): a field guard whose
/// receiver flows through an intermediate reference local that is
/// `&mut`-borrowed (alias-reseatable, e.g. `let mut r=o; mem::swap(&mut r,
/// &mut r2); check(r)`) must NOT resolve the subject to the pinned param —
/// `r` may point elsewhere at the call. `guard_receiver_subject` now
/// pin-checks every hop, so the guard does not connect and the field unwrap
/// stays fail-closed (never a false PROVE via the wrong subject).
#[test]
fn field_guard_through_aliased_reseat_does_not_connect() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const CHECK: &str = "mycrate::S::check";
    let s_adt = || Ty::Adt { adt_kind: None, layout: None, 
        name: "mycrate::S".into(),
        fields: vec![("slot".into(), std_option_ty())],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let ref_s = || Ty::Ref { mutable: false, inner: Box::new(s_adt()) };
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: ref_s(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: ref_s(), name: Some("r".into()) },
            // _3 = &mut _2 : the alias that reseats r (unpins _2).
            LocalDecl {
                index: 3,
                ty: Ty::Ref { mutable: true, inner: Box::new(ref_s()) },
                name: Some("m".into()),
            },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 5, ty: std_option_ty(), name: Some("rv".into()) },
            LocalDecl { index: 6, ty: Ty::u64(), name: Some("res".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Ref { mutable: true, place: Place::local(2) },
                        span: SourceSpan::default(),
                    },
                ],
                terminator: call_term(CHECK, vec![Operand::Copy(Place::local(2))], 4, 1),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(4)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(5),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Field(0)],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(5))],
                    6,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    let mut map = trust_types::fx::FxHashMap::default();
    map.insert(
        CHECK.to_string(),
        super::ReturnBoolPredSummary {
            enum_name: "core::option::Option".into(),
            params: vec!["self".into()],
            pred_param: 1,
            pred_field: Some(0),
            kind: super::ReturnBoolPredKind::Iff,
            pred_tag: 1,
            pred_is_eq: true,
            variants: vec![0, 1],
        },
    );
    let _summary_scope = enter_bool_pred_summaries(map);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    let defs = v2_build_path_definition_map(&func);
    let at_unwrap = format!("{:?}", defs.get(&BlockId(2)).cloned().unwrap_or_default());
    // The soundness property: the reseated guard must NOT connect, so its
    // `(g ∧ tag==Some)` fact must NOT reach the unwrap block and cannot
    // discharge the obligation (no false PROVE).
    assert!(
        !at_unwrap.contains("\"g\""),
        "the alias-reseated guard fact must NOT be threaded to the field unwrap: {at_unwrap}"
    );
    // With the guard disconnected the field tag is FREE ⇒ the unwrap refutes
    // over `o.slot == None` (sound: o.slot is genuinely unpinned here), never
    // a discharged proof.
    assert_eq!(
        vcs.len(),
        1,
        "the field unwrap must refute over the free tag, not be discharged"
    );
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "o*.0.0", 0)),
        "refutation over the free field tag, not a guard discharge: {:?}",
        vcs[0].formula
    );
}

/// SOUNDNESS regression (audit r3 sibling): the UNWRAP-side field resolver
/// (`unwrap_field_place`) has the same aliased-reseat exposure — a temp
/// copied from a field then `&mut`-reseated (`t = x.slot; m = &mut t;
/// opaque(m); t.unwrap()`) has a stale `copy((*x).slot)` def while the unwrap
/// operates on the mutated value. It must FAIL-CLOSED (not resolve to the
/// stale field, which a guard on `x.slot` could then falsely discharge).
#[test]
fn unwrap_field_place_rejects_aliased_reseated_temp() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const OPAQUE: &str = "mycrate::opaque";
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Ref {
                    mutable: false,
                    inner: Box::new(Ty::Adt { adt_kind: None, layout: None, 
                        name: "mycrate::S".into(),
                        fields: vec![("slot".into(), std_option_ty())],
                        variants: vec![],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, }),
                },
                name: Some("x".into()),
            },
            LocalDecl { index: 2, ty: std_option_ty(), name: Some("t".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Ref { mutable: true, inner: Box::new(std_option_ty()) },
                name: Some("m".into()),
            },
            LocalDecl { index: 4, ty: Ty::Unit, name: Some("u".into()) },
            LocalDecl { index: 5, ty: Ty::u64(), name: Some("res".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref, Projection::Field(0)],
                        })),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Ref { mutable: true, place: Place::local(2) },
                        span: SourceSpan::default(),
                    },
                ],
                terminator: call_term(OPAQUE, vec![Operand::Move(Place::local(3))], 4, 1),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(2))],
                    5,
                    2,
                ),
            },
            ret_block(2),
        ],
        1,
    );
    // The reseated temp cannot be resolved to `(*x).slot`; the unwrap stays
    // fail-closed (no field refutation over a stale subject).
    assert!(
        generate_unwrap_panic_freedom_vcs(&func).is_empty(),
        "a &mut-reseated unwrap temp must not resolve to the stale field"
    );
    assert_eq!(unverified_row_count(&func), 1, "the reseated-temp unwrap stays fail-closed");
}

/// (2e) Eq-guard channel: `if o == None { 0 } else { o.unwrap() }` with the
/// promoted-const shape (`_g = eq(&o, _c)` where `_c`'s unique def is the
/// recovered `UnitVariantRef` constant). The modeled eq is a CONNECTED
/// observer, shape (d) fires, and the eq semantics + range reach the unwrap
/// block over the SHARED tag term.
#[test]
fn param_unwrap_guarded_by_eq_none_const_connects() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const PARTIAL_EQ: &str = "std::cmp::PartialEq::eq";
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: Ty::Unit, name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Unit, name: Some("c".into()) },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 5, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(
                            trust_types::ConstValue::UnitVariantRef {
                                enum_name: "core::option::Option".into(),
                                variant: 0,
                            },
                        )),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: call_term(
                    PARTIAL_EQ,
                    vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(3))],
                    4,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(4)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(3),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    5,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1, "modeled eq must be whitelisted; shape (d) must fire");
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "o.0", 0)),
        "the body must test the SHARED entry tag against None: {:?}",
        vcs[0].formula
    );
    assert_eq!(unverified_row_count(&func), 0, "the fail-closed row is replaced");
    let defs = v2_build_path_definition_map(&func);
    let at_unwrap = format!("{:?}", defs.get(&BlockId(2)).cloned().unwrap_or_default());
    assert!(
        at_unwrap.contains("\"o.0\"") && at_unwrap.contains("\"g\""),
        "eq semantics over the shared tag must reach the unwrap block: {at_unwrap}"
    );
}

/// (2f) Eq-guard fail-closed: equality against a PAYLOAD-CARRYING variant
/// (`o == Some(5)` — a one-operand construction) is never a pure tag test;
/// the eq stays an OPAQUE observer and the fail-closed row remains.
#[test]
fn eq_some_payload_pin_fails_closed() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const PARTIAL_EQ: &str = "std::cmp::PartialEq::eq";
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: Ty::Unit, name: Some("b".into()) },
            LocalDecl { index: 3, ty: std_option_ty(), name: Some("n".into()) },
            LocalDecl { index: 4, ty: Ty::Unit, name: Some("nb".into()) },
            LocalDecl { index: 5, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 6, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    },
                    // `Some(5)` — a PAYLOAD-carrying construction.
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "core::option::Option".into(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Constant(ConstValue::Int(5))],
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(3) },
                        span: SourceSpan::default(),
                    },
                ],
                terminator: call_term(
                    PARTIAL_EQ,
                    vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(4))],
                    5,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(5)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    6,
                    4,
                ),
            },
            ret_block(3),
            ret_block(4),
        ],
        1,
    );
    assert!(
        generate_unwrap_panic_freedom_vcs(&func).is_empty(),
        "a payload-carrying eq pin must stay an opaque observer"
    );
    assert_eq!(unverified_row_count(&func), 1, "fail-closed row must remain");
}

/// (2g) F1 (fires-only as_ref exemption): an as_ref whose RESULT is
/// reassigned does NOT connect (`unwrap_tag_origin` fails on the unpinned
/// dest), so the as_ref call stays an OPAQUE observer and the fail-closed
/// row remains — never a free-tag refutation for a guarded-but-unconnected
/// chain.
#[test]
fn as_ref_result_unpinned_fails_closed() {
    const OPTION_UNWRAP: &str = "core::option::Option::<T>::unwrap";
    const OPTION_AS_REF: &str = "core::option::Option::<T>::as_ref";
    const OPTION_IS_SOME: &str = "core::option::Option::<T>::is_some";
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl { index: 2, ty: Ty::Unit, name: Some("b".into()) },
            LocalDecl { index: 3, ty: std_option_ty(), name: Some("t".into()) },
            LocalDecl { index: 4, ty: Ty::Unit, name: Some("tb".into()) },
            LocalDecl { index: 5, ty: Ty::Bool, name: Some("g".into()) },
            LocalDecl { index: 6, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    OPTION_AS_REF,
                    vec![Operand::Move(Place::local(2))],
                    3,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                // REASSIGN the as_ref dest — the hop must not connect.
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(3) },
                        span: SourceSpan::default(),
                    },
                ],
                terminator: call_term(
                    OPTION_IS_SOME,
                    vec![Operand::Move(Place::local(4))],
                    5,
                    2,
                ),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(5)),
                    targets: vec![(0, BlockId(4))],
                    otherwise: BlockId(3),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![],
                terminator: call_term(
                    OPTION_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    6,
                    5,
                ),
            },
            ret_block(4),
            ret_block(5),
        ],
        1,
    );
    assert!(
        generate_unwrap_panic_freedom_vcs(&func).is_empty(),
        "an unconnected as_ref must stay an opaque observer (F1)"
    );
    assert_eq!(unverified_row_count(&func), 1, "fail-closed row must remain");
}

/// (2c) Shape-(d) observer gate: a COPY of the receiver observed by a
/// discriminant read (`let c = r; match c { … } … r.unwrap()`) keeps the
/// fail-closed row — the copy's guard could dominate the unwrap through a
/// channel this lane does not connect to the free entry-tag variable, so a
/// free-tag refutation would risk a spurious ground counterexample.
#[test]
fn copied_receiver_observer_keeps_unsupported_row() {
    let mut func = guarded_result_unwrap_fn();
    func.body.locals.push(LocalDecl { index: 4, ty: std_result_ty(), name: Some("c".into()) });
    func.body.blocks[0].stmts = vec![
        Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Discriminant(Place::local(4)),
            span: SourceSpan::default(),
        },
    ];
    func.body.blocks[0].terminator =
        call_term(RESULT_UNWRAP, vec![Operand::Move(Place::local(1))], 3, 1);
    func.body.blocks.truncate(2);
    func.body.blocks[1] = ret_block(1);
    assert!(
        generate_unwrap_panic_freedom_vcs(&func).is_empty(),
        "the observer gate must fail closed (no free-tag refutation)"
    );
    assert_eq!(unverified_row_count(&func), 1, "fail-closed row must remain");
}

/// (3) Non-std receiver types NEVER model: a user enum named like Result
/// (wrong def-path), a Result missing the `__tag` slot, and a receiver with
/// no variant defs all keep the UnsupportedMir row.
#[test]
fn non_std_or_unmodeled_receiver_stays_unsupported() {
    // (a) user enum: right shape, wrong def-path.
    let mut user_enum = guarded_result_unwrap_fn();
    if let Ty::Adt { name, .. } = &mut user_enum.body.locals[1].ty {
        *name = "mycrate::Result".into();
    }
    assert!(generate_unwrap_panic_freedom_vcs(&user_enum).is_empty());
    assert_eq!(unverified_row_count(&user_enum), 1);

    // (b) std name but the flattened `__tag` slot is absent.
    let mut no_tag = guarded_result_unwrap_fn();
    if let Ty::Adt { fields, .. } = &mut no_tag.body.locals[1].ty {
        fields.retain(|(n, _)| n != "__tag");
    }
    assert!(generate_unwrap_panic_freedom_vcs(&no_tag).is_empty());
    assert_eq!(unverified_row_count(&no_tag), 1);

    // (c) std name but no variant defs (a degraded / pre-P4 lowering).
    let mut no_variants = guarded_result_unwrap_fn();
    if let Ty::Adt { variants, .. } = &mut no_variants.body.locals[1].ty {
        variants.clear();
    }
    assert!(generate_unwrap_panic_freedom_vcs(&no_variants).is_empty());
    assert_eq!(unverified_row_count(&no_variants), 1);
}

/// (3b) A USER extension-trait `unwrap` on a genuine std Option/Result
/// receiver has ARBITRARY panic semantics (it may panic on Ok!): the callee
/// path anchor rejects it and the fail-closed row stays.
#[test]
fn user_extension_trait_unwrap_stays_unsupported() {
    let mut func = guarded_result_unwrap_fn();
    if let Terminator::Call { func: callee, .. } = &mut func.body.blocks[1].terminator {
        *callee = "mycrate::ResultExt::unwrap".into();
    }
    assert!(generate_unwrap_panic_freedom_vcs(&func).is_empty());
    assert_eq!(
        unverified_row_count(&func),
        1,
        "a user `unwrap` (path contains `Result` but is not the std method) \
         must keep the fail-closed row"
    );
}

/// (4) `expect` behaves exactly like `unwrap` (Option flavor: panic tag is
/// `None` = 0, pinned by the dominating `Some` (= 1) switch arm).
#[test]
fn guarded_option_expect_gets_unsat_shaped_vc() {
    let func = func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_option_ty(), name: Some("o".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::Int { width: 64, signed: true },
                name: Some("d".into()),
            },
            LocalDecl { index: 3, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(1, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: call_term(
                    OPTION_EXPECT,
                    vec![
                        Operand::Move(Place::local(1)),
                        Operand::Constant(ConstValue::Int(0)), // the message operand
                    ],
                    3,
                    3,
                ),
            },
            ret_block(2),
            ret_block(3),
        ],
        1,
    );
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(
        matches!(&vcs[0].kind, VcKind::Assertion { message } if message == "Call::expect::panic-freedom")
    );
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "d", 0)),
        "body must assert the None tag `d == 0`: {:?}",
        vcs[0].formula
    );
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "d", 1)),
        "the dominating Some guard `d == 1` must be conjoined: {:?}",
        vcs[0].formula
    );
    assert_eq!(unverified_row_count(&func), 0);
}

/// Construction-pinned fixture: `let r = <variant>(7); r.unwrap()`.
fn construction_pinned_fn(variant: usize) -> VerifiableFunction {
    func_of(
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: std_result_ty(), name: Some("r".into()) },
            LocalDecl { index: 2, ty: Ty::u64(), name: Some("x".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "core::result::Result".into(),
                            variant,
                            active_field: None,
                            args: None,
                        },
                        vec![Operand::Constant(ConstValue::Int(7))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: call_term(
                    RESULT_UNWRAP,
                    vec![Operand::Move(Place::local(1))],
                    2,
                    1,
                ),
            },
            ret_block(1),
        ],
        0,
    )
}

/// (b-shape, safe) `let r = Ok(7); r.unwrap()`: the tag is GROUND-pinned to
/// the Ok tag, so the body is the trivially-UNSAT `0 == 1`.
#[test]
fn ok_construction_pinned_unwrap_is_ground_unsat() {
    let func = construction_pinned_fn(0);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_int_int(f, 0, 1)),
        "Ok-constructed receiver must yield the ground body `0 == 1`: {:?}",
        vcs[0].formula
    );
    assert_eq!(unverified_row_count(&func), 0);
}

/// (b-shape, GENUINE PANIC) `let r = Err(7); r.unwrap()`: the body is the
/// trivially-SAT `1 == 1` — refutation-grade, the row can never prove.
#[test]
fn err_construction_pinned_unwrap_stays_sat_shaped() {
    let func = construction_pinned_fn(1);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(
        has_and_conjunct(&vcs[0].formula, &|f| eq_int_int(f, 1, 1)),
        "Err-constructed receiver must yield the SAT body `1 == 1`: {:?}",
        vcs[0].formula
    );
    assert_eq!(unverified_row_count(&func), 0);
}

/// SOUNDNESS GATE: a `mut` PARAMETER receiver with a body store has TWO
/// values — the guard could pin the pre-store tag while the call sees the
/// post-store one. Never modeled; the fail-closed row stays.
#[test]
fn reassigned_mut_param_receiver_falls_back() {
    let mut func = guarded_result_unwrap_fn();
    // `r = Err(())` between the read and the switch — r is param _1.
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "core::result::Result".into(),
                variant: 1,
                active_field: None,
                args: None,
            },
            vec![Operand::Constant(ConstValue::Int(0))],
        ),
        span: SourceSpan::default(),
    });
    assert!(
        generate_unwrap_panic_freedom_vcs(&func).is_empty(),
        "a reassigned mut param receiver must never be modeled"
    );
    assert_eq!(unverified_row_count(&func), 1);
}

/// SOUNDNESS GATE: a `&mut`-borrowed receiver can have its payload/tag
/// mutated through the alias — never modeled.
#[test]
fn mut_borrowed_receiver_falls_back() {
    let mut func = guarded_result_unwrap_fn();
    func.body.locals.push(LocalDecl {
        index: 4,
        ty: Ty::Ref { mutable: true, inner: Box::new(std_result_ty()) },
        name: None,
    });
    func.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
            span: SourceSpan::default(),
        },
    );
    assert!(generate_unwrap_panic_freedom_vcs(&func).is_empty());
    assert_eq!(unverified_row_count(&func), 1);
}

/// The compiler-inserted receiver temp (`_t = move r; unwrap(move _t)`) is
/// traced back to the guarded origin `r`, so the real MIR spelling of the
/// guarded idiom still proves.
#[test]
fn receiver_move_hop_traces_to_guarded_origin() {
    let mut func = guarded_result_unwrap_fn();
    func.body.locals.push(LocalDecl { index: 4, ty: std_result_ty(), name: Some("t".into()) });
    func.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
        span: SourceSpan::default(),
    });
    func.body.blocks[1].terminator =
        call_term(RESULT_UNWRAP, vec![Operand::Move(Place::local(4))], 3, 3);
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1, "the hop must trace to the pinned origin");
    assert!(has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "d", 1)));
    assert!(has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "d", 0)));
    assert_eq!(unverified_row_count(&func), 0);
}

/// The `is_ok`-inlined shape reads the discriminant THROUGH a shared borrow
/// (`b = &r; d = discriminant(*b)`): still recognized (a shared borrow
/// cannot mutate the pinned receiver).
#[test]
fn discriminant_read_through_shared_borrow_is_recognized() {
    let mut func = guarded_result_unwrap_fn();
    func.body.locals.push(LocalDecl {
        index: 4,
        ty: Ty::Ref { mutable: false, inner: Box::new(std_result_ty()) },
        name: Some("b".into()),
    });
    func.body.blocks[0].stmts = vec![
        Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Discriminant(Place {
                local: 4,
                projections: vec![Projection::Deref],
            }),
            span: SourceSpan::default(),
        },
    ];
    let vcs = generate_unwrap_panic_freedom_vcs(&func);
    assert_eq!(vcs.len(), 1, "the shared-borrow read shape must be recognized");
    assert!(has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "d", 1)));
    assert!(has_and_conjunct(&vcs[0].formula, &|f| eq_var_int(f, "d", 0)));
    assert_eq!(unverified_row_count(&func), 0);
}

/// End-to-end through `generate_vcs`: the guarded fixture yields the
/// solvable Assertion VC and NO `panic-freedom-unverified` row anywhere in
/// the full stream (the two lanes key on the same recognizer).
#[test]
fn generate_vcs_swaps_row_for_solvable_vc() {
    let func = guarded_result_unwrap_fn();
    let vcs = super::generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Assertion { message }
            if message == "Call::unwrap::panic-freedom")),
        "the solvable panic-freedom VC must flow through generate_vcs"
    );
    assert!(
        !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
            if kind.ends_with("::panic-freedom-unverified"))),
        "the fail-closed row must be replaced, not doubled"
    );
}
