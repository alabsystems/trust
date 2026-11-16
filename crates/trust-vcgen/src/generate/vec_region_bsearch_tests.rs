// Trust (W4 fix round 1, 2026-09-25): the `binary_search` result facts
// (`vec_region::slice_binary_search_result_definitions`) and the one place-name
// channel that has to kill them.
//
// THE DEFECT. The facts `Ok.0 < len` / `Err.0 <= len` are stated over the payload
// NAME `r@0.0` / `r@1.0`. They were seeded with no stability gate on `r`, and the
// place-name algebra did not treat `@` (the `Downcast` spelling) as a projection
// separator, so NO write of `r` — an aggregate `r = Ok(big)`, a move `r = tmp`, a
// second call `r = w.binary_search(..)` — killed them. Measured end to end on
// `0.10.0+g0a25d1c42` as four kernel-certified false proofs (probes r12..r12d,
// `tests/ui/trust/vec_bsearch_result_stale_fact.rs`).
//
// Two independent closures, pinned separately so that losing either is visible:
//  (1) the producer seeds only when the call is `r`'s ONE definition and `r` is
//      stable (`seeds_*` below);
//  (2) the path-definition fixpoint kills a fact over `r@v.k` at any whole write
//      of `r` (`a_whole_write_of_the_result_kills_*` below), driven with a
//      HAND-SEEDED fact so it tests the kill with the producer's gate out of the
//      way — plus a positive control showing the seeded fact does reach the use
//      when nothing writes `r`.

use trust_types::fx::FxHashMap;
use trust_types::{
    AggregateKind, BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue,
    Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VariantDef, VerifiableBody,
    VerifiableFunction,
};

const BSEARCH: &str = "core::slice::<impl [T]>::binary_search";

fn result_usize_ty() -> Ty {
    Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        name: "core::result::Result<usize, usize>".into(),
        fields: vec![
            ("__tag".into(), Ty::Int { width: 64, signed: true }),
            ("__v0_0".into(), Ty::usize()),
            ("__v1_0".into(), Ty::usize()),
        ]
        .into(),
        variants: vec![
            VariantDef {
                name: "Ok".into(),
                discriminant: 0,
                fields: vec![("0".into(), Ty::usize())],
            },
            VariantDef {
                name: "Err".into(),
                discriminant: 1,
                fields: vec![("0".into(), Ty::usize())],
            },
        ]
        .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    }
}

fn bsearch_call(dest: usize, target: BlockId) -> Terminator {
    Terminator::Call {
        func: BSEARCH.into(),
        args: vec![Operand::Copy(Place::local(1)), Operand::Move(Place::local(7))],
        dest: Place::local(dest),
        target: Some(target),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(BSEARCH),
        is_foreign: false,
        unwind: UnwindEdge::Unreachable,
    }
}

fn ok_payload(local: usize) -> Place {
    Place { local, projections: vec![Projection::Downcast(0), Projection::Field(0)] }
}

fn ok_of(op: Operand) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt { name: "Result".into(), variant: 0, active_field: None, args: None },
        vec![op],
    )
}

/// How the `Ok` arm rewrites the result before the payload is read again.
#[derive(Clone, Copy, Debug)]
enum Rewrite {
    /// Nothing: `r` keeps the search's value (the safe shape).
    None,
    /// `r = Ok(big)` — an aggregate whole write (r12b / r12d).
    Aggregate,
    /// `tmp = Ok(big); r = move tmp` — a whole `Use` write.
    Move,
    /// `r = xs.binary_search(..)` again — a call-destination whole write (r12c).
    Call,
}

/// `fn f(xs: &[u32], x: u32, big: usize) -> usize`
///   bb0: xr = &x; r = binary_search(copy xs, move xr) -> bb1
///   bb1: d = discriminant(r); switchInt(d) -> [0: bb2, 1: bb3, otherwise: bb4]
///   bb2 (Ok arm): <rewrite of r>; -> bb5
///   bb3: return          bb4: unreachable
///   bb5: j = copy (r as Ok).0; return
fn search_then_rewrite(rewrite: Rewrite) -> VerifiableFunction {
    let span = SourceSpan::default;
    let arm_stmts = match rewrite {
        Rewrite::None | Rewrite::Call => vec![],
        Rewrite::Aggregate => vec![Statement::Assign {
            place: Place::local(4),
            rvalue: ok_of(Operand::Copy(Place::local(3))),
            span: span(),
        }],
        Rewrite::Move => vec![
            Statement::Assign {
                place: Place::local(8),
                rvalue: ok_of(Operand::Copy(Place::local(3))),
                span: span(),
            },
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::Use(Operand::Move(Place::local(8))),
                span: span(),
            },
        ],
    };
    let arm_terminator = match rewrite {
        Rewrite::Call => bsearch_call(4, BlockId(5)),
        _ => Terminator::Goto(BlockId(5)),
    };
    let xr = || Statement::Assign {
        place: Place::local(7),
        rvalue: Rvalue::Ref { mutable: false, place: Place::local(2) },
        span: span(),
    };
    let mut arm_stmts = arm_stmts;
    if matches!(rewrite, Rewrite::Call) {
        arm_stmts.push(xr());
    }
    VerifiableFunction {
        name: "f".into(),
        def_path: "test::bsearch_rewrite".into(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: Some("ret".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
                    },
                    name: Some("xs".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("big".into()) },
                LocalDecl { index: 4, ty: result_usize_ty(), name: Some("r".into()) },
                LocalDecl { index: 5, ty: Ty::isize(), name: Some("d".into()) },
                LocalDecl { index: 6, ty: Ty::usize(), name: Some("j".into()) },
                LocalDecl {
                    index: 7,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("xr".into()),
                },
                LocalDecl { index: 8, ty: result_usize_ty(), name: Some("tmp".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![xr()],
                    terminator: bsearch_call(4, BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::Discriminant(Place::local(4)),
                        span: span(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(2)), (1, BlockId(3))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: true,
                        span: span(),
                    },
                },
                BasicBlock { id: BlockId(2), stmts: arm_stmts, terminator: arm_terminator },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Unreachable },
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::Use(Operand::Copy(ok_payload(4))),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::usize(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Is `f` a `<`/`<=` bound whose left side is the payload name `payload`?
fn is_payload_bound(f: &Formula, payload: &str) -> bool {
    matches!(f, Formula::Lt(lhs, _) | Formula::Le(lhs, _)
        if matches!(lhs.as_ref(), Formula::Var(name, _) if name == payload))
}

#[test]
fn seeds_both_arms_when_the_call_is_the_results_only_definition() {
    let func = search_then_rewrite(Rewrite::None);
    let facts = super::slice_binary_search_result_definitions(&func);
    let ok_arm = facts.get(&BlockId(2)).cloned().unwrap_or_default();
    let err_arm = facts.get(&BlockId(3)).cloned().unwrap_or_default();
    assert!(
        ok_arm.iter().any(|f| matches!(f, Formula::Lt(..)) && is_payload_bound(f, "r@0.0")),
        "the Ok arm must carry `r@0.0 < len` (the precision this lane exists for); got {ok_arm:?}"
    );
    assert!(
        err_arm.iter().any(|f| matches!(f, Formula::Le(..)) && is_payload_bound(f, "r@1.0")),
        "the Err arm must carry `r@1.0 <= len`; got {err_arm:?}"
    );
}

#[test]
fn seeds_nothing_when_the_result_is_written_again() {
    for rewrite in [Rewrite::Aggregate, Rewrite::Move, Rewrite::Call] {
        let func = search_then_rewrite(rewrite);
        let facts = super::slice_binary_search_result_definitions(&func);
        assert!(
            facts.values().all(Vec::is_empty),
            "{rewrite:?}: `r` has a second definition, so no payload fact may be seeded; got {facts:?}"
        );
    }
}

#[test]
fn seeds_nothing_when_the_result_is_mutably_borrowed() {
    // `let p = &mut r;` anywhere: the payload can change behind the name.
    let mut func = search_then_rewrite(Rewrite::None);
    func.body.locals.push(LocalDecl {
        index: 9,
        ty: Ty::Ref { mutable: true, inner: Box::new(result_usize_ty()) },
        name: Some("p".into()),
    });
    func.body.blocks[3].stmts.push(Statement::Assign {
        place: Place::local(9),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(4) },
        span: SourceSpan::default(),
    });
    let facts = super::slice_binary_search_result_definitions(&func);
    assert!(
        facts.values().all(Vec::is_empty),
        "a `&mut r` escape must withhold the facts; got {facts:?}"
    );
}

fn seeded_ok_bound() -> FxHashMap<BlockId, Vec<Formula>> {
    let fact = Formula::Lt(
        Box::new(Formula::Var("r@0.0".into(), Sort::Int)),
        Box::new(Formula::Var("xs__slice_len".into(), Sort::Int)),
    );
    FxHashMap::from_iter([(BlockId(2), vec![fact])])
}

#[test]
fn a_seeded_payload_bound_reaches_the_use_when_nothing_writes_the_result() {
    // POSITIVE CONTROL for the kill tests below: without it, "the fact is absent at
    // bb5" could mean the seed never flows at all.
    let func = search_then_rewrite(Rewrite::None);
    let result = super::v2_path_def_fixpoint(&func, &seeded_ok_bound());
    let at_use = result.get(&BlockId(5)).cloned().unwrap_or_default();
    assert!(
        at_use.iter().any(|f| is_payload_bound(f, "r@0.0")),
        "control: the seeded `r@0.0 < len` must reach bb5 unkilled; got {at_use:?}"
    );
}

#[test]
fn a_whole_write_of_the_result_kills_a_fact_over_its_payload() {
    for rewrite in [Rewrite::Aggregate, Rewrite::Move, Rewrite::Call] {
        let func = search_then_rewrite(rewrite);
        let result = super::v2_path_def_fixpoint(&func, &seeded_ok_bound());
        let at_use = result.get(&BlockId(5)).cloned().unwrap_or_default();
        assert!(
            !at_use.iter().any(|f| is_payload_bound(f, "r@0.0")),
            "{rewrite:?}: a whole write of `r` must kill the stale `r@0.0 < len`; got {at_use:?}"
        );
    }
}
