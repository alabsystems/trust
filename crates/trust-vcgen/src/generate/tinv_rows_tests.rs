//! TINV step 7.5: the row shim, on hand-built bodies.
//!
//! Every produced row is checked to replay exactly (`record.reconstruct() == formula`);
//! the semantic assertions solve the row with the in-process ay router.

use std::collections::HashSet;

use trust_types::{
    AggregateKind, AssertMessage, BasicBlock, BinOp, BlockId, CalleeIdentity, ConstValue, Formula,
    LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty,
    TypeInvariantPoint, TypeInvariantSite, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition, VerificationResult,
};

use super::*;
use crate::type_invariant::obligations::{BodyTinvPlan, TinvBodyRows, type_invariant_check_vcs};
use crate::type_invariant::unwind::NoExactModels;
use crate::type_invariant::{CandidateConjunct, FieldTerm, TinvType, field_var};

// ---------------------------------------------------------------------------------------
// Bodies
// ---------------------------------------------------------------------------------------

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn vec_ty() -> Ty {
    Ty::Seq { elem: Box::new(Ty::Int { width: 8, signed: false }), drop_auth: None }
}

fn adt(name: &str, fields: &[(&str, Ty)]) -> Ty {
    Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: name.into(),
        fields: fields.iter().map(|(n, t)| (n.to_string(), t.clone())).collect::<Vec<_>>().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `c::P { i: u64, n: u64, k: u64 }`, the json-Parser-like linear shape.
fn p_fields() -> Vec<(&'static str, Ty)> {
    vec![("i", u64_ty()), ("n", u64_ty()), ("k", u64_ty())]
}

fn p_ty() -> Ty {
    adt("c::P", &p_fields())
}

/// `I(P) = i <= n`, conjunct 0.
fn p_tinv() -> TinvType {
    TinvType {
        def_path: "c::P".into(),
        fields: p_fields().into_iter().map(|(n, t)| (n.to_string(), t)).collect(),
        conjuncts: vec![CandidateConjunct {
            id: 0,
            formula: Formula::Le(
                Box::new(field_var(FieldTerm::Value(0))),
                Box::new(field_var(FieldTerm::Value(1))),
            ),
        }],
    }
}

/// `c::S { v: Vec<u8>, k: u64 }` with `I(S) = k <= len(v)`.
fn s_fields() -> Vec<(&'static str, Ty)> {
    vec![("v", vec_ty()), ("k", u64_ty())]
}

fn s_tinv() -> TinvType {
    TinvType {
        def_path: "c::S".into(),
        fields: s_fields().into_iter().map(|(n, t)| (n.to_string(), t)).collect(),
        conjuncts: vec![CandidateConjunct {
            id: 0,
            formula: Formula::Le(
                Box::new(field_var(FieldTerm::Value(1))),
                Box::new(field_var(FieldTerm::Len(0))),
            ),
        }],
    }
}

fn mut_ref(t: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(t) }
}

fn func(
    name: &str,
    locals: Vec<(Ty, Option<&str>)>,
    arg_count: usize,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("c::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: locals[0].0.clone(),
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, (ty, name))| LocalDecl { index, ty, name: name.map(Into::into) })
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

/// A `u64` constant, as the extractor spells one.
fn konst(v: i128) -> Operand {
    Operand::Constant(ConstValue::Uint(v as u128, 64))
}

/// `(*_l).f`.
fn self_field(l: usize, f: usize) -> Place {
    Place { local: l, projections: vec![Projection::Deref, Projection::Field(f)] }
}

fn field(l: usize, f: usize) -> Place {
    Place { local: l, projections: vec![Projection::Field(f)] }
}

fn goto(t: usize) -> Terminator {
    Terminator::Goto(BlockId(t))
}

fn switch(discr: usize, zero: usize, otherwise: usize) -> Terminator {
    Terminator::SwitchInt {
        discr: Operand::Move(Place::local(discr)),
        targets: vec![(0, BlockId(zero))],
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

/// `assert(!move _l.1) -> target`, the overflow check of a checked add into `_l`.
fn overflow_assert(l: usize, target: usize) -> Terminator {
    Terminator::Assert {
        cond: Operand::Move(field(l, 1)),
        expected: false,
        msg: AssertMessage::Overflow(BinOp::Add),
        target: BlockId(target),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Continue,
    }
}

fn call(args: Vec<Operand>, dest: Place, target: usize, id: Option<CalleeIdentity>) -> Terminator {
    Terminator::Call {
        func: "c::g".into(),
        args,
        dest,
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Continue,
        callee_identity: id,
        callee_key: None,
    }
}

const INV: CalleeIdentity =
    CalleeIdentity { stable_crate_id: 1, def_index: 7, substs_digest: [0, 0] };

/// The three lowerings of `bump` the tests use.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Bump {
    /// `if self.i < self.n { self.i += 1 }` with the Return in the write block (the
    /// tail-duplicated shape; the else edge returns from its own block).
    Guarded,
    /// The same method as rustc lowers it at `-O0`: the write block and the else edge
    /// JOIN at one Return block.
    GuardedJoin,
    /// `self.i += 1` with no guard.
    Unguarded,
}

/// `fn bump(&mut self) { if self.i < self.n { self.i += 1 } }` on `P { i, n, k }` (debug
/// MIR: a checked add and its overflow assert before the write).
fn bump(shape: Bump) -> VerifiableFunction {
    // _0: (), _1: &mut P, _2: u64, _3: u64, _4: bool, _5: (u64, bool)
    let locals = vec![
        (Ty::Unit, None),
        (mut_ref(p_ty()), Some("self")),
        (u64_ty(), None),
        (u64_ty(), None),
        (Ty::Bool, None),
        (Ty::Tuple(vec![u64_ty(), Ty::Bool]), None),
    ];
    let add = blk(
        1,
        vec![assign(
            Place::local(5),
            Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(self_field(1, 0)), konst(1)),
        )],
        overflow_assert(5, 2),
    );
    let write_stmt = assign(self_field(1, 0), Rvalue::Use(Operand::Move(field(5, 0))));
    let write = match shape {
        Bump::Guarded => blk(2, vec![write_stmt], Terminator::Return),
        Bump::GuardedJoin | Bump::Unguarded => blk(2, vec![write_stmt], goto(3)),
    };
    let ret = blk(3, vec![], Terminator::Return);
    let entry = match shape {
        Bump::Guarded | Bump::GuardedJoin => blk(
            0,
            vec![
                assign(Place::local(2), Rvalue::Use(Operand::Copy(self_field(1, 0)))),
                assign(Place::local(3), Rvalue::Use(Operand::Copy(self_field(1, 1)))),
                assign(
                    Place::local(4),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Move(Place::local(2)),
                        Operand::Move(Place::local(3)),
                    ),
                ),
            ],
            switch(4, 3, 1),
        ),
        Bump::Unguarded => blk(0, vec![], goto(1)),
    };
    let name = match shape {
        Bump::Guarded => "bump",
        Bump::GuardedJoin => "bump_join",
        Bump::Unguarded => "bump_unguarded",
    };
    func(name, locals, 1, vec![entry, add, write, ret])
}

fn plan_run(
    f: &VerifiableFunction,
    types: &[TinvType],
    inventory: &HashSet<CalleeIdentity>,
    may_drop: &dyn Fn(&Ty) -> bool,
    steps: u64,
) -> Result<TinvBodyRows, crate::type_invariant::obligations::TinvObligationRefusal> {
    let plan = BodyTinvPlan {
        types,
        facts: None,
        inventory,
        models: &NoExactModels,
        may_run_user_drop: may_drop,
        step_budget: steps,
    };
    type_invariant_check_vcs(f, &plan)
}

/// Every TINV row of `f` for `types`, with every record checked to replay exactly.
fn rows_of(f: &VerifiableFunction, types: &[TinvType]) -> Vec<(TinvRowKey, VerificationCondition)> {
    rows_with(f, types, &HashSet::new())
}

fn rows_with(
    f: &VerifiableFunction,
    types: &[TinvType],
    inventory: &HashSet<CalleeIdentity>,
) -> Vec<(TinvRowKey, VerificationCondition)> {
    let out = plan_run(f, types, inventory, &|_| true, u64::MAX).expect("tinv rows");
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    assert!(out.uninstantiable.is_empty(), "{:?}", out.uninstantiable);
    for (key, vc) in &out.rows {
        let record = vc.obligation.as_ref().expect("every TINV row carries a record");
        assert_eq!(record.reconstruct().as_ref(), Some(&vc.formula), "{key:?} must replay exactly");
        let VcKind::TypeInvariant { ty, point, site, conjunct, ordinal, edge } = &vc.kind else {
            panic!("{:?}", vc.kind)
        };
        assert_eq!(
            (ty, *point, *site, *conjunct, *ordinal, *edge),
            (&key.ty, key.point, key.site, key.conjunct, key.ordinal, key.edge)
        );
        // Since 7.7 the kind gate admits the kind: the VC-level verdict IS the row gate.
        assert_eq!(vc.kernel_authority_refusal(), vc.type_invariant_situatedness_refusal());
    }
    out.rows
}

fn only(
    rows: &[(TinvRowKey, VerificationCondition)],
    point: TypeInvariantPoint,
) -> &VerificationCondition {
    let hits: Vec<_> = rows.iter().filter(|(k, _)| k.point == point).collect();
    assert_eq!(
        hits.len(),
        1,
        "exactly one {point} row: {:?}",
        rows.iter().map(|r| &r.0).collect::<Vec<_>>()
    );
    &hits[0].1
}

/// Solve `formula` (a violation formula: UNSAT = the invariant holds) with the in-process
/// ay router, on a thread with room for generation-sized formulas.
fn solve(formula: &Formula) -> VerificationResult {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "tinv oracle".into() },
        function: "tinv".into(),
        location: SourceSpan::default(),
        formula: formula.clone(),
        contract_metadata: None,
        obligation: None,
    };
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let router = crate::test_router::deterministic_test_router();
            router.verify_all(std::slice::from_ref(&vc)).into_iter().next().expect("one verdict").1
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn assert_unsat(vc: &VerificationCondition) {
    let r = solve(&vc.formula);
    assert!(
        matches!(r, VerificationResult::Proved { .. }),
        "expected UNSAT: {r:?}\n{:?}",
        vc.formula
    );
}

fn assert_sat(vc: &VerificationCondition) {
    let r = solve(&vc.formula);
    assert!(
        matches!(r, VerificationResult::Failed { .. }),
        "expected SAT: {r:?}\n{:?}",
        vc.formula
    );
}

fn mentions(f: &Formula, needle: &str) -> bool {
    let mut hit = false;
    f.visit(&mut |n| {
        if let Formula::Var(name, _) = n
            && name.contains(needle)
        {
            hit = true;
        }
    });
    hit
}

// ---------------------------------------------------------------------------------------
// (i) Ordinary generation is byte-identical
// ---------------------------------------------------------------------------------------

fn fixture(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"));
    serde_json::from_str(&std::fs::read_to_string(path).expect("fixture")).expect("deserialize")
}

fn dump(vcs: &[VerificationCondition]) -> Vec<String> {
    vcs.iter().map(|vc| format!("{:?} {:?} {:?}", vc.kind, vc.formula, vc.obligation)).collect()
}

#[test]
fn ordinary_generation_is_byte_identical_with_and_without_a_request() {
    let bodies = vec![
        fixture("abs_guarded.json"),
        fixture("bounded_copy_min_mir.json"),
        fixture("tinv_mut_pointee_entry_rename_mir.json"),
        fixture("chunks_index_mir.json"),
        fixture("countdown_fmt_u32_macro_mir.json"),
        fixture("charindices_plus_one_mir.json"),
        fixture("contract_inc_mir.json"),
        fixture("cex_grounding_mutescape_unminable_default_mir.json"),
        fixture("adapter_yield_windows_all_closure_mir.json"),
        fixture("countdown_cursor_reseat_mir.json"),
        bump(Bump::Guarded),
        bump(Bump::GuardedJoin),
        bump(Bump::Unguarded),
    ];
    for f in &bodies {
        let plain = crate::generate_vcs(f);
        assert!(!plain.iter().any(|vc| matches!(vc.kind, VcKind::TypeInvariant { .. })));
        // An installed request with no rows, owned by THIS body: the hooks run and push
        // nothing.
        let same_owner = {
            let _g = enter_tinv_rows(Rc::new(TinvRowRequest::new(
                f.def_path.clone(),
                Vec::new(),
                Vec::new(),
            )));
            crate::generate_vcs(f)
        };
        assert_eq!(dump(&plain), dump(&same_owner), "{}", f.def_path);
        // A request owned by ANOTHER body (with rows): the hooks do nothing at all.
        let other = rows_request_for(&bump(Bump::Guarded));
        let foreign = {
            let _g = enter_tinv_rows(Rc::new(other));
            crate::generate_vcs(f)
        };
        if f.def_path != "c::bump" {
            assert_eq!(dump(&plain), dump(&foreign), "{}", f.def_path);
        }
    }
}

/// A non-empty request for `f` built exactly as `type_invariant_check_vcs` builds it.
fn rows_request_for(f: &VerifiableFunction) -> TinvRowRequest {
    use crate::type_invariant::obligations::{
        SigmaSource, TinvInputs, obligation_points, sigma_of_root,
    };
    let ty = p_tinv();
    let inventory = HashSet::new();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    let points = obligation_points(f, None, &inp).expect("points");
    let rows = points
        .into_iter()
        .map(|point| {
            assert!(matches!(point.sigma_src, SigmaSource::Root));
            let sigma = sigma_of_root(f, &ty, &point.root);
            let core = crate::type_invariant::instantiate(&ty.conjuncts[0], &sigma).expect("core");
            RequestRow {
                key: TinvRowKey {
                    ty: ty.def_path.clone(),
                    conjunct: 0,
                    point: point.point,
                    site: point.site,
                    ordinal: 0,
                    edge: None,
                },
                ty: 0,
                point,
                sigma,
                core,
                edge_guard: None,
            }
        })
        .collect();
    TinvRowRequest::new(
        f.def_path.clone(),
        vec![RequestType {
            def_path: ty.def_path.clone(),
            post_calls: Vec::new(),
            constructions: Vec::new(),
            arm_facts: Vec::new(),
        }],
        rows,
    )
}

// ---------------------------------------------------------------------------------------
// The 0(b)(c) linear shape: `i <= n` preserved by `i += 1` under `i < n`
// ---------------------------------------------------------------------------------------

#[test]
fn guarded_bump_return_row_is_unsat_and_situated() {
    let rows = rows_of(&bump(Bump::Guarded), &[p_tinv()]);
    // The write dirties `*self`; nothing else is owed (the overflow assert precedes it,
    // and the else edge returns clean).
    assert_eq!(rows.len(), 1, "{:?}", rows.iter().map(|r| &r.0).collect::<Vec<_>>());
    let r = only(&rows, TypeInvariantPoint::Return);
    assert_eq!(r.type_invariant_situatedness_refusal(), None, "{:?}", r.obligation);
    assert_unsat(r);
}

/// TINV-9(a). rustc's join lowering of the same method: the R point at the join bb3 is
/// split into one edge part per predecessor (bb0's skip edge under `!(i < n)`, bb2's write
/// edge). Each part is built at its predecessor's terminal by the ordinary walk, is
/// situated, replays, and is UNSAT; the point is discharged because EVERY part is. Before
/// the split the single row read the free merge token `self*.0#e_s2_0` and was unsituated.
#[test]
fn guarded_bump_join_return_point_is_split_and_every_part_is_unsat_and_situated() {
    let rows = rows_of(&bump(Bump::GuardedJoin), &[p_tinv()]);
    let parts: Vec<_> =
        rows.iter().filter(|(k, _)| k.point == TypeInvariantPoint::Return).collect();
    assert_eq!(
        parts.iter().map(|(k, _)| (k.site, k.edge)).collect::<Vec<_>>(),
        vec![
            (TypeInvariantSite { block: 3, statement_index: 0 }, Some(0)),
            (TypeInvariantSite { block: 3, statement_index: 0 }, Some(2)),
        ]
    );
    for (k, vc) in &parts {
        assert_eq!(vc.type_invariant_situatedness_refusal(), None, "{k:?}: {:?}", vc.obligation);
        assert!(!mentions(&vc.formula, "self*.0#e_s2_0"), "{k:?}: {:?}", vc.formula);
        assert_unsat(vc);
    }
    // The skip part carries the switch's routing condition as a hypothesis.
    let skip = &parts[0].1.obligation.as_ref().expect("record").body;
    assert!(matches!(skip, Formula::And(h) if h.len() >= 2), "{skip:?}");
}

/// The via-bb2 part inherits the decoration of the tail-Return lowering's bb2 row: the two
/// prefixes (bb0 -> bb1 -> bb2) and write sets are identical, so the records are, but for
/// the part's Goto-edge guard slot (`true`, the FIRST body conjunct).
#[test]
fn the_write_edge_part_is_the_tail_return_row() {
    let join = rows_of(&bump(Bump::GuardedJoin), &[p_tinv()]);
    let tail = rows_of(&bump(Bump::Guarded), &[p_tinv()]);
    let part = join.iter().find(|(k, _)| k.edge == Some(2)).expect("the via-bb2 part");
    let row = only(&tail, TypeInvariantPoint::Return);
    let (pr, rr) =
        (part.1.obligation.as_ref().expect("record"), row.obligation.as_ref().expect("record"));
    assert_eq!(pr.wrappers, rr.wrappers);
    let slotted = match &rr.body {
        Formula::And(h) => {
            Formula::And(std::iter::once(Formula::Bool(true)).chain(h.iter().cloned()).collect())
        }
        other => Formula::And(vec![Formula::Bool(true), other.clone()]),
    };
    assert_eq!(pr.body, slotted);
}

/// `fn bump_any(&mut self, c: bool) { if c { self.i += 1 } }` in the join lowering: the
/// guard is unrelated to `i < n`, so the write part is SAT and the point is NOT discharged
/// although the skip part is UNSAT.
fn bump_join_unrelated() -> VerifiableFunction {
    let locals = vec![
        (Ty::Unit, None),
        (mut_ref(p_ty()), Some("self")),
        (Ty::Bool, Some("c")),
        (Ty::Tuple(vec![u64_ty(), Ty::Bool]), None),
    ];
    func(
        "bump_any",
        locals,
        2,
        vec![
            blk(0, vec![], switch(2, 3, 1)),
            blk(
                1,
                vec![assign(
                    Place::local(3),
                    Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(self_field(1, 0)), konst(1)),
                )],
                overflow_assert(3, 2),
            ),
            blk(
                2,
                vec![assign(self_field(1, 0), Rvalue::Use(Operand::Move(field(3, 0))))],
                goto(3),
            ),
            blk(3, vec![], Terminator::Return),
        ],
    )
}

#[test]
fn an_unguarded_join_keeps_a_sat_part_so_the_point_is_not_discharged() {
    let rows = rows_of(&bump_join_unrelated(), &[p_tinv()]);
    let parts: Vec<_> =
        rows.iter().filter(|(k, _)| k.point == TypeInvariantPoint::Return).collect();
    assert_eq!(parts.iter().map(|(k, _)| k.edge).collect::<Vec<_>>(), vec![Some(0), Some(2)]);
    assert_unsat(&parts[0].1);
    assert_sat(&parts[1].1);
}

/// `dirty_join(kind)`: `self.k = 0` opens the window in bb0, which routes on `c` to bb2 or
/// through bb1 (a Call or Drop terminator) to bb2, the Return.
fn dirty_join(term: Terminator) -> VerifiableFunction {
    func(
        "dirty_join",
        vec![
            (Ty::Unit, None),
            (mut_ref(p_ty()), Some("self")),
            (Ty::Bool, Some("c")),
            (Ty::Unit, None),
            (vec_ty(), Some("w")),
        ],
        2,
        vec![
            blk(0, vec![assign(self_field(1, 2), Rvalue::Use(konst(0)))], switch(2, 2, 1)),
            blk(1, vec![], term),
            blk(2, vec![], Terminator::Return),
        ],
    )
}

fn split_of(f: &VerifiableFunction) -> Vec<Result<Vec<(usize, Option<Formula>)>, String>> {
    let req = rows_request_for(f);
    let sv = super::stmt_versions_for(f);
    req.rows.iter().map(|row| join_parts(f, &sv, row)).collect()
}

fn r_split_of(f: &VerifiableFunction) -> Result<Vec<(usize, Option<Formula>)>, String> {
    let req = rows_request_for(f);
    let rows: Vec<_> =
        req.rows.iter().filter(|r| r.point.point == TypeInvariantPoint::Return).collect();
    assert_eq!(rows.len(), 1, "one R row");
    r_split_at(f, rows[0].point.site.block)
}

fn r_split_at(
    f: &VerifiableFunction,
    block: usize,
) -> Result<Vec<(usize, Option<Formula>)>, String> {
    let req = rows_request_for(f);
    let sv = super::stmt_versions_for(f);
    let rows: Vec<_> = req
        .rows
        .iter()
        .filter(|r| r.point.point == TypeInvariantPoint::Return && r.point.site.block == block)
        .collect();
    assert_eq!(rows.len(), 1, "one R row at bb{block}");
    join_parts(f, &sv, rows[0])
}

#[test]
fn a_join_with_a_call_or_drop_predecessor_edge_keeps_the_single_row() {
    let call_edge = dirty_join(call(Vec::new(), Place::local(3), 2, None));
    let drop_edge = dirty_join(Terminator::Drop {
        place: Place::local(4),
        target: BlockId(2),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Continue,
    });
    for f in [call_edge, drop_edge] {
        let why = r_split_of(&f).expect_err("a Call/Drop edge refuses the split");
        assert!(why.starts_with("G3"), "{why}");
        let rows = rows_of(&f, &[p_tinv()]);
        let r: Vec<_> =
            rows.iter().filter(|(k, _)| k.point == TypeInvariantPoint::Return).collect();
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].0.edge, None);
    }
}

#[test]
fn a_join_whose_block_rebinds_a_core_name_keeps_the_single_row() {
    // bb3: `self.i = self.n; return`: the join's own prefix rebinds `(*self).i`.
    let mut f = bump(Bump::GuardedJoin);
    f.body.blocks[3]
        .stmts
        .push(assign(self_field(1, 0), Rvalue::Use(Operand::Copy(self_field(1, 1)))));
    let why = r_split_of(&f).expect_err("G2");
    assert!(why.starts_with("G2"), "{why}");
    let rows = rows_of(&f, &[p_tinv()]);
    let r: Vec<_> = rows.iter().filter(|(k, _)| k.point == TypeInvariantPoint::Return).collect();
    assert_eq!(r.len(), 1);
    assert_eq!(r[0].0.edge, None);
}

#[test]
fn a_join_with_an_unreachable_predecessor_keeps_the_single_row() {
    // A dead bb4 also jumps to the join: it is no reachable predecessor (G1).
    let mut f = bump(Bump::GuardedJoin);
    f.body.blocks.push(blk(4, vec![], goto(3)));
    let why = r_split_of(&f).expect_err("G1");
    assert!(why.starts_with("G1"), "{why}");
}

#[test]
fn a_join_over_the_fan_in_cap_keeps_the_single_row() {
    // bb0: `self.k = 0`, then a switch on `_2: u64` to bb1..=bb17 (otherwise bb18); each
    // of those goes to the Return bb19: 18 predecessors.
    let mut blocks = vec![blk(
        0,
        vec![assign(self_field(1, 2), Rvalue::Use(konst(0)))],
        Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(2)),
            targets: (1..=17).map(|v| (v as u128, BlockId(v))).collect(),
            otherwise: BlockId(18),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    )];
    blocks.extend((1..=18).map(|b| blk(b, vec![], goto(19))));
    blocks.push(blk(19, vec![], Terminator::Return));
    let f = func(
        "fan",
        vec![(Ty::Unit, None), (mut_ref(p_ty()), Some("self")), (u64_ty(), None)],
        2,
        blocks,
    );
    let why = r_split_of(&f).expect_err("G5");
    assert!(why.starts_with("G5"), "{why}");
    // Two fewer predecessors (16) is within the cap and splits.
    let mut g = f.clone();
    g.body.blocks[0].terminator = Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(2)),
        targets: (1..=15).map(|v| (v as u128, BlockId(v))).collect(),
        otherwise: BlockId(16),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    g.body.blocks[17].terminator = Terminator::Return;
    g.body.blocks[18].terminator = Terminator::Return;
    assert_eq!(r_split_at(&g, 19).expect("16 parts").len(), 16);
}

#[test]
fn the_entry_block_is_never_split() {
    // bb0 (`self.k = 0; return`) is the R point and two dead blocks jump to it: the
    // implicit entry edge (G1).
    let f = func(
        "entry_join",
        vec![(Ty::Unit, None), (mut_ref(p_ty()), Some("self"))],
        1,
        vec![
            blk(0, vec![assign(self_field(1, 2), Rvalue::Use(konst(0)))], Terminator::Return),
            blk(1, vec![], goto(0)),
            blk(2, vec![], goto(0)),
        ],
    );
    let req = rows_request_for(&f);
    let sv = super::stmt_versions_for(&f);
    let r = req.rows.iter().find(|r| r.point.point == TypeInvariantPoint::Return).expect("R");
    let why = join_parts(&f, &sv, r).expect_err("G1");
    assert!(why.starts_with("G1"), "{why}");
    // No other row kind is ever split.
    for got in split_of(&f) {
        assert!(got.is_err());
    }
}

/// `match x { 0 | 1 => {}, _ => { self.i = self.n } }` lowered with the two values routing to
/// the join: the skip edge's guard is the DISJUNCTION, never the conjunction, of the
/// routing values. The conjunction would be UNSAT, a vacuous part.
#[test]
fn an_or_pattern_edge_guard_is_a_disjunction() {
    let f = func(
        "orpat",
        vec![(Ty::Unit, None), (mut_ref(p_ty()), Some("self")), (u64_ty(), Some("x"))],
        2,
        vec![
            blk(
                0,
                vec![assign(self_field(1, 2), Rvalue::Use(konst(0)))],
                Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, BlockId(2)), (1, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            blk(
                1,
                vec![assign(self_field(1, 0), Rvalue::Use(Operand::Copy(self_field(1, 1))))],
                goto(2),
            ),
            blk(2, vec![], Terminator::Return),
        ],
    );
    let parts = r_split_of(&f).expect("split");
    assert_eq!(parts.iter().map(|(p, _)| *p).collect::<Vec<_>>(), vec![0, 1]);
    let Some(Formula::Or(alts)) = &parts[0].1 else { panic!("{:?}", parts[0].1) };
    assert_eq!(alts.len(), 2);
    let conj = VerificationCondition {
        kind: VcKind::Assertion { message: "planted".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::And(alts.clone()),
        contract_metadata: None,
        obligation: None,
    };
    assert_unsat(&conj);
    // The real parts: both UNSAT (the skip edge leaves `*self` at its entry value, the
    // write edge sets `i = n`), each situated.
    let rows = rows_of(&f, &[p_tinv()]);
    for (k, vc) in rows.iter().filter(|(k, _)| k.point == TypeInvariantPoint::Return) {
        assert!(k.edge.is_some());
        assert_eq!(vc.type_invariant_situatedness_refusal(), None, "{k:?}");
        assert_unsat(vc);
    }
}

/// `fn stale(&mut self, x: u64) { let c = self.i >= self.n; self.i = x; if c { self.i =
/// self.n } }` in one block before the switch: the compared FIELD is written between the
/// compare and the switch. The skip edge (`c == false`) leaves `self.i == x` arbitrary, so
/// its part is a real violation (SAT). A guard built by resolving `c` to its comparison
/// (`!(self.i >= self.n)`) and renamed at bb0's terminal reads the POST-write `self.i`,
/// i.e. `x < n`: over-strong, and the part was a FALSE UNSAT before the edge guard was
/// built from the raw discriminant.
fn stale_compare_join() -> VerifiableFunction {
    func(
        "stale",
        vec![
            (Ty::Unit, None),
            (mut_ref(p_ty()), Some("self")),
            (Ty::Bool, None),
            (u64_ty(), Some("x")),
        ],
        2,
        vec![
            blk(
                0,
                vec![
                    assign(
                        Place::local(2),
                        Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(self_field(1, 0)),
                            Operand::Copy(self_field(1, 1)),
                        ),
                    ),
                    assign(self_field(1, 0), Rvalue::Use(Operand::Copy(Place::local(3)))),
                ],
                switch(2, 2, 1),
            ),
            blk(
                1,
                vec![assign(self_field(1, 0), Rvalue::Use(Operand::Copy(self_field(1, 1))))],
                goto(2),
            ),
            blk(2, vec![], Terminator::Return),
        ],
    )
}

#[test]
fn a_compared_field_written_before_the_switch_does_not_strengthen_the_edge_guard() {
    let f = stale_compare_join();
    let rows = rows_of(&f, &[p_tinv()]);
    let r: Vec<_> = rows.iter().filter(|(k, _)| k.point == TypeInvariantPoint::Return).collect();
    assert_eq!(r.iter().map(|(k, _)| k.edge).collect::<Vec<_>>(), vec![Some(0), Some(1)]);
    // The skip part is a real violation; the write part holds.
    assert_sat(&r[0].1);
    assert_unsat(&r[1].1);
    // The guard is the RAW discriminant, never its (stale) comparison.
    let parts = r_split_of(&f).expect("split");
    assert_eq!(parts.iter().map(|(p, _)| *p).collect::<Vec<_>>(), vec![0, 1]);
    let guard = parts[0].1.as_ref().expect("the skip edge is guarded");
    assert!(!mentions(guard, "self"), "{guard:?}");
}

#[test]
fn ordinary_rows_are_unchanged_by_a_split_request() {
    let f = bump(Bump::GuardedJoin);
    let plain = crate::generate_vcs(&f);
    let mut req = rows_request_for(&f);
    {
        let _scope = super::FuncAnalysisScope::enter(&f);
        let sv = super::stmt_versions_for(&f);
        req.split_join_returns(&f, &sv);
    }
    assert!(req.rows.iter().filter(|r| r.key.edge.is_some()).count() == 2);
    let with = {
        let _g = enter_tinv_rows(Rc::new(req));
        crate::generate_vcs(&f)
    };
    let ordinary: Vec<_> =
        with.into_iter().filter(|vc| !matches!(vc.kind, VcKind::TypeInvariant { .. })).collect();
    assert_eq!(dump(&plain), dump(&ordinary));
}

#[test]
fn the_coverage_match_refuses_a_missing_or_foreign_edge_part() {
    let mut p0 = key(TypeInvariantPoint::Return, 3, 0);
    p0.edge = Some(0);
    let mut p2 = p0.clone();
    p2.edge = Some(2);
    let requested = vec![p0.clone(), p2.clone()];
    let got = match_coverage(&requested, vec![row(&p2), row(&p0)]).expect("by identity");
    assert_eq!(got.iter().map(|(k, _)| k.edge).collect::<Vec<_>>(), vec![Some(0), Some(2)]);
    assert!(matches!(
        match_coverage(&requested, vec![row(&p0)]),
        Err(TinvObligationRefusal::Coverage { expected: 2, got: 1 })
    ));
    let mut p1 = p0.clone();
    p1.edge = Some(1);
    assert!(matches!(
        match_coverage(&requested, vec![row(&p0), row(&p1)]),
        Err(TinvObligationRefusal::Coverage { .. })
    ));
    // The whole row does not stand in for the parts.
    let whole = key(TypeInvariantPoint::Return, 3, 0);
    assert!(matches!(
        match_coverage(&requested, vec![row(&whole), row(&p0)]),
        Err(TinvObligationRefusal::Coverage { .. })
    ));
}

#[test]
fn unguarded_bump_return_row_is_sat() {
    let rows = rows_of(&bump(Bump::Unguarded), &[p_tinv()]);
    assert_sat(only(&rows, TypeInvariantPoint::Return));
}

// ---------------------------------------------------------------------------------------
// E at an aggregate with constant operands
// ---------------------------------------------------------------------------------------

/// `fn new() -> P { P { i, n, k: 0 } }`.
fn new_p(i: i128, n: i128) -> VerifiableFunction {
    func(
        "new",
        vec![(p_ty(), None)],
        0,
        vec![blk(
            0,
            vec![assign(
                Place::local(0),
                Rvalue::Aggregate(
                    AggregateKind::Adt {
                        name: "c::P".into(),
                        variant: 0,
                        active_field: None,
                        args: None,
                    },
                    vec![konst(i), konst(n), konst(0)],
                ),
            )],
            Terminator::Return,
        )],
    )
}

#[test]
fn establish_row_at_a_constant_aggregate_follows_the_constants() {
    let ok = rows_of(&new_p(3, 5), &[p_tinv()]);
    let e = only(&ok, TypeInvariantPoint::Establish);
    assert_eq!(rows_key_site(&ok), vec![TypeInvariantSite { block: 0, statement_index: 0 }]);
    assert_unsat(e);
    let bad = rows_of(&new_p(7, 5), &[p_tinv()]);
    assert_sat(only(&bad, TypeInvariantPoint::Establish));
    // MEASURED, recorded: a CLOSED core (every σ term a literal) names no program state,
    // and the 7.2 structural gate refuses it as unsituated.
    assert!(e.type_invariant_situatedness_refusal().is_some());
}

fn rows_key_site(rows: &[(TinvRowKey, VerificationCondition)]) -> Vec<TypeInvariantSite> {
    rows.iter().map(|(k, _)| k.site).collect()
}

// ---------------------------------------------------------------------------------------
// U at an Assert inside the window
// ---------------------------------------------------------------------------------------

/// `fn bump2(&mut self) { self.k = 0; self.i += 1 }`: `k = 0` opens the window, so the
/// overflow assert owes U, and the write of `i` comes after it.
fn bump2() -> VerifiableFunction {
    let locals = vec![
        (Ty::Unit, None),
        (mut_ref(p_ty()), Some("self")),
        (Ty::Tuple(vec![u64_ty(), Ty::Bool]), None),
    ];
    func(
        "bump2",
        locals,
        1,
        vec![
            blk(
                0,
                vec![
                    assign(self_field(1, 2), Rvalue::Use(konst(0))),
                    assign(
                        Place::local(2),
                        Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(self_field(1, 0)),
                            konst(1),
                        ),
                    ),
                ],
                overflow_assert(2, 1),
            ),
            blk(
                1,
                vec![assign(self_field(1, 0), Rvalue::Use(Operand::Move(field(2, 0))))],
                Terminator::Return,
            ),
        ],
    )
}

#[test]
fn unwind_row_at_an_assert_before_the_write_is_unsat() {
    let rows = rows_of(&bump2(), &[p_tinv()]);
    let u = only(&rows, TypeInvariantPoint::Unwind);
    let VcKind::TypeInvariant { site, .. } = &u.kind else { unreachable!() };
    assert_eq!(*site, TypeInvariantSite { block: 0, statement_index: 2 });
    // The failure condition is a hypothesis of the row body.
    let body = &u.obligation.as_ref().expect("record").body;
    assert!(mentions(body, "_2.1"), "{body:?}");
    assert_eq!(u.type_invariant_situatedness_refusal(), None);
    assert_unsat(u);
    // The R row at bb1 is unguarded `i + 1 <= n`: SAT.
    assert_sat(only(&rows, TypeInvariantPoint::Return));
}

// ---------------------------------------------------------------------------------------
// (vi) A block with both terminator and statement rows
// ---------------------------------------------------------------------------------------

/// `fn mixed(&mut self) { let q = P { i: 1, n: 2, k: 0 }; self.k = 3; }` in one block:
/// E at bb0[0] (a statement row) and R at bb0's Return (a terminator row, emitted FIRST).
fn mixed() -> VerifiableFunction {
    func(
        "mixed",
        vec![(Ty::Unit, None), (mut_ref(p_ty()), Some("self")), (p_ty(), None)],
        1,
        vec![blk(
            0,
            vec![
                assign(
                    Place::local(2),
                    Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "c::P".into(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        vec![konst(1), konst(2), konst(0)],
                    ),
                ),
                assign(self_field(1, 2), Rvalue::Use(konst(3))),
            ],
            Terminator::Return,
        )],
    )
}

#[test]
fn a_block_with_terminator_and_statement_rows_passes_the_coverage_match() {
    let rows = rows_of(&mixed(), &[p_tinv()]);
    let points: Vec<_> = rows.iter().map(|(k, _)| (k.point, k.site.statement_index)).collect();
    // Request order (E, then R), whatever order the walk emitted them in.
    assert_eq!(points, vec![(TypeInvariantPoint::Establish, 0), (TypeInvariantPoint::Return, 2)]);
    assert_unsat(only(&rows, TypeInvariantPoint::Establish));
    // `k = 3` leaves `i <= n` alone: the entry assumption carries it to the Return.
    let r = only(&rows, TypeInvariantPoint::Return);
    assert_eq!(r.type_invariant_situatedness_refusal(), None);
    assert_unsat(r);
}

fn key(point: TypeInvariantPoint, block: usize, stmt: usize) -> TinvRowKey {
    TinvRowKey {
        ty: "c::P".into(),
        conjunct: 0,
        point,
        site: TypeInvariantSite { block, statement_index: stmt },
        ordinal: 0,
        edge: None,
    }
}

fn row(k: &TinvRowKey) -> (BlockId, VerificationCondition) {
    (
        BlockId(k.site.block),
        VerificationCondition {
            kind: VcKind::TypeInvariant {
                ty: k.ty.clone(),
                point: k.point,
                site: k.site,
                conjunct: k.conjunct,
                ordinal: k.ordinal,
                edge: k.edge,
            },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
    )
}

#[test]
fn the_coverage_match_is_keyed_and_refuses_missing_extra_and_degraded_rows() {
    let e = key(TypeInvariantPoint::Establish, 0, 0);
    let r = key(TypeInvariantPoint::Return, 0, 2);
    let requested = vec![e.clone(), r.clone()];
    // Emitted terminator-first, the walk's order: matched by key.
    let got = match_coverage(&requested, vec![row(&r), row(&e)]).expect("keyed match");
    assert_eq!(got.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>(), requested);
    // A missing row.
    assert!(matches!(
        match_coverage(&requested, vec![row(&r)]),
        Err(TinvObligationRefusal::Coverage { expected: 2, got: 1 })
    ));
    // An extra row.
    assert!(matches!(
        match_coverage(&requested, vec![row(&r), row(&e), row(&e)]),
        Err(TinvObligationRefusal::Coverage { .. })
    ));
    // (vii) A row the degraded path-guard replacement turned into `UnsupportedMir`.
    let mut degraded = row(&e);
    degraded.1.kind =
        VcKind::UnsupportedMir { kind: "PathConditionDegraded".into(), detail: String::new() };
    assert!(matches!(
        match_coverage(&requested, vec![row(&r), degraded]),
        Err(TinvObligationRefusal::Coverage { expected: 2, got: 1 })
    ));
    // Two rows that differ only in ordinal pair by their OWN identity, whatever order
    // they are emitted in: never positionally.
    let mut e1 = e.clone();
    e1.ordinal = 1;
    let mut a = row(&e);
    a.1.formula = Formula::Bool(false);
    let got = match_coverage(&[e.clone(), e1.clone()], vec![row(&e1), a]).expect("pairs");
    assert_eq!(got[0].0, e);
    assert_eq!(got[0].1.formula, Formula::Bool(false));
    assert_eq!(got[1].0, e1);
    assert_eq!(got[1].1.formula, Formula::Bool(true));
    // A row of the right (ty, point, site) but another ordinal is not a match, nor is a
    // second row for a filled key.
    assert!(matches!(
        match_coverage(&[e.clone(), e1.clone()], vec![row(&e), row(&e)]),
        Err(TinvObligationRefusal::Coverage { expected: 2, got: 1 })
    ));
    // Conjunct and edge are identity too.
    let mut c1 = e.clone();
    c1.conjunct = 1;
    assert!(matches!(
        match_coverage(std::slice::from_ref(&e), vec![row(&c1)]),
        Err(TinvObligationRefusal::Coverage { expected: 1, got: 0 })
    ));
    let mut part = r.clone();
    part.edge = Some(0);
    assert!(matches!(
        match_coverage(std::slice::from_ref(&r), vec![row(&part)]),
        Err(TinvObligationRefusal::Coverage { expected: 1, got: 0 })
    ));
    // A duplicate requested key refuses outright.
    assert!(matches!(
        match_coverage(&[e.clone(), e.clone()], vec![row(&e), row(&e)]),
        Err(TinvObligationRefusal::Coverage { .. })
    ));
}

// ---------------------------------------------------------------------------------------
// (iii) U havoc spelling
// ---------------------------------------------------------------------------------------

/// `fn ext(&mut self) { self.k = 0; g(&mut *self); }` with `g` OUTSIDE the inventory:
/// the call owes C and a U row whose state havocs `*self`.
fn ext(id: Option<CalleeIdentity>) -> VerifiableFunction {
    func(
        "ext",
        vec![
            (Ty::Unit, None),
            (mut_ref(p_ty()), Some("self")),
            (mut_ref(p_ty()), None),
            (Ty::Unit, None),
        ],
        1,
        vec![
            blk(
                0,
                vec![
                    assign(self_field(1, 2), Rvalue::Use(konst(0))),
                    assign(
                        Place::local(2),
                        Rvalue::Ref {
                            mutable: true,
                            place: Place { local: 1, projections: vec![Projection::Deref] },
                        },
                    ),
                ],
                call(vec![Operand::Move(Place::local(2))], Place::local(3), 1, id),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    )
}

#[test]
fn an_unwind_row_at_a_call_havocs_with_the_tinvu_family_and_survives_normalization() {
    let f = ext(None);
    let rows = rows_of(&f, &[p_tinv()]);
    let u = only(&rows, TypeInvariantPoint::Unwind);
    // Every σ name the call may write is the block's havoc symbol, never a successor
    // version token, and the final normalize left it alone.
    assert!(mentions(&u.formula, "self*.0#tinvu_s0"), "{:?}", u.formula);
    assert!(mentions(&u.formula, "self*.1#tinvu_s0"), "{:?}", u.formula);
    assert!(!mentions(&u.formula, "self*.0#s"), "{:?}", u.formula);
    // A havocked core is bound by no hypothesis: unsituated, and SAT.
    assert!(u.type_invariant_situatedness_refusal().is_some());
    assert_sat(u);
    // The C row before it is the pre-call state: `k = 0` keeps `i <= n`.
    assert_unsat(only(&rows, TypeInvariantPoint::Call));
}

#[test]
fn the_ssa_collapse_exempts_tinv_unwind_havocs_of_a_whole_ssa_local() {
    // `_2` is written once: its version tokens collapse to the bare name, its TINV unwind
    // havoc must not.
    let f = func(
        "ssa",
        vec![(Ty::Unit, None), (u64_ty(), None), (u64_ty(), None)],
        1,
        vec![blk(
            0,
            vec![assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1))))],
            Terminator::Return,
        )],
    );
    assert!(super::discharge::local_versions_collapse_to_bare(&f, 2));
    let v = |n: &str| Formula::var_owned(n.to_string(), trust_types::Sort::Int);
    let ssa = Formula::Eq(Box::new(v("_2#s0_0")), Box::new(v("_2#tinvu_s0")));
    let norm = normalize_ssa_version_tokens(&f, &ssa);
    assert_eq!(norm, Formula::Eq(Box::new(v("_2")), Box::new(v("_2#tinvu_s0"))));
    let guard = super::discharge::bare_ssa_guard_variant(&f, &ssa).expect("one rename fires");
    assert_eq!(guard, norm);
    assert!(crate::version_token_is_tinv_unwind_havoc("_2#tinvu_a3"));
    assert!(!crate::version_token_is_tinv_unwind_havoc("_2#s0_0"));
    assert!(!crate::version_token_is_tinv_unwind_havoc("_2"));
}

// ---------------------------------------------------------------------------------------
// Drop-and-replace on the unwind edge
// ---------------------------------------------------------------------------------------

/// `fn reset(&mut self, w: Vec<u8>) { self.k = 0; self.v = w; }`: the window is open at the
/// drop of the old `v`, whose cleanup writes `w` into it.
fn reset() -> VerifiableFunction {
    let s = adt("c::S", &s_fields());
    let v = Place { local: 1, projections: vec![Projection::Deref, Projection::Field(0)] };
    func(
        "reset",
        vec![(Ty::Unit, None), (mut_ref(s), Some("self")), (vec_ty(), Some("w"))],
        2,
        vec![
            blk(
                0,
                vec![assign(self_field(1, 1), Rvalue::Use(konst(0)))],
                Terminator::Drop {
                    place: v.clone(),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Continue,
                },
            ),
            blk(
                1,
                vec![assign(v, Rvalue::Use(Operand::Move(Place::local(2))))],
                Terminator::Return,
            ),
        ],
    )
}

#[test]
fn a_drop_and_replace_unwind_row_binds_the_overwritten_field_to_the_havocked_operand() {
    let rows = rows_of(&reset(), &[s_tinv()]);
    let u = only(&rows, TypeInvariantPoint::Unwind);
    // `v` (the Len term `self*.0`) is overwritten by the replacement; `k` is havocked by
    // the drop glue's `&mut self` reach.
    assert!(mentions(&u.formula, "self*.0#tinvu_a0"), "{:?}", u.formula);
    assert!(mentions(&u.formula, "self*.1#tinvu_s0"), "{:?}", u.formula);
    let body = &u.obligation.as_ref().expect("record").body;
    let Formula::And(parts) = body else { panic!("{body:?}") };
    assert!(
        parts.iter().any(|p| matches!(p, Formula::Eq(l, _) if mentions(l, "self*.0#tinvu_a0"))),
        "{body:?}"
    );
}

// ---------------------------------------------------------------------------------------
// (v) Post-call facts
// ---------------------------------------------------------------------------------------

/// `fn twice(&mut self) { self.k = 0; inv(&mut *self); self.k = 1; }`: after the inventory
/// call, `I(*self)` is assumed at its single-predecessor target bb1, which dominates the
/// Return. The call havocs `*self`, so only that fact can prove the R row.
fn twice(id: Option<CalleeIdentity>) -> VerifiableFunction {
    let mut f = ext(id);
    f.name = "twice".into();
    f.def_path = "c::twice".into();
    f.body.blocks[1].stmts.push(assign(self_field(1, 2), Rvalue::Use(konst(1))));
    f
}

#[test]
fn a_post_call_fact_proves_the_return_after_an_inventory_call() {
    let inventory: HashSet<CalleeIdentity> = [INV].into_iter().collect();
    let rows = rows_with(&twice(Some(INV)), &[p_tinv()], &inventory);
    // No U row at the inventory call (it discharges U for the root it received).
    assert!(!rows.iter().any(|(k, _)| k.point == TypeInvariantPoint::Unwind));
    let r = only(&rows, TypeInvariantPoint::Return);
    let body = &r.obligation.as_ref().expect("record").body;
    let Formula::And(parts) = body else { panic!("expected a post-call fact in {body:?}") };
    assert!(parts.len() >= 2, "{body:?}");
    assert_eq!(r.type_invariant_situatedness_refusal(), None);
    assert_unsat(r);

    // The same call outside the inventory: no fact, the window stays open through the
    // havoc, and R is refuted.
    let rows = rows_of(&twice(None), &[p_tinv()]);
    assert_sat(only(&rows, TypeInvariantPoint::Return));
}

/// `twice` with the inventory callee receiving `&*self`, and `self.i = self.n` after it:
/// the shared protected reborrow does not havoc `*self`, so at bb1 the post-call fact
/// reads the entry value of `(*self).i`, a name the body versions later; the seal spells it
/// `#e` so the row's own rename cannot re-stamp it with the post-write token.
#[test]
fn a_post_call_fact_with_entry_valued_reads_is_sealed_with_the_entry_sentinel() {
    let mut f = twice(Some(INV));
    f.name = "twice_shared".into();
    f.def_path = "c::twice_shared".into();
    f.body.locals[2].ty = Ty::Ref { mutable: false, inner: Box::new(p_ty()) };
    f.body.blocks[0].stmts[1] = assign(
        Place::local(2),
        Rvalue::Ref {
            mutable: false,
            place: Place { local: 1, projections: vec![Projection::Deref] },
        },
    );
    f.body.blocks[1]
        .stmts
        .push(assign(self_field(1, 0), Rvalue::Use(Operand::Copy(self_field(1, 1)))));
    let inventory: HashSet<CalleeIdentity> = [INV].into_iter().collect();
    let rows = rows_with(&f, &[p_tinv()], &inventory);
    let r = only(&rows, TypeInvariantPoint::Return);
    let body = &r.obligation.as_ref().expect("record").body;
    let Formula::And(parts) = body else { panic!("expected a post-call fact in {body:?}") };
    assert!(parts.len() >= 2 && mentions(&parts[0], "self*.0#e"), "{body:?}");
    assert_eq!(r.type_invariant_situatedness_refusal(), None);
    assert_unsat(r);
}

#[test]
fn a_post_call_fact_is_not_attached_where_the_target_does_not_dominate() {
    // bb0: switch -> bb1 | bb2; bb1: k = 0; inv(&mut *self) -> bb3; bb2: k = 0; goto bb4;
    // bb3: goto bb4; bb4: return. bb3 (the call's target) does not dominate bb4.
    let locals = vec![
        (Ty::Unit, None),
        (mut_ref(p_ty()), Some("self")),
        (Ty::Bool, Some("c")),
        (mut_ref(p_ty()), None),
        (Ty::Unit, None),
    ];
    let f = func(
        "split",
        locals,
        2,
        vec![
            blk(0, vec![], switch(2, 2, 1)),
            blk(
                1,
                vec![
                    assign(self_field(1, 2), Rvalue::Use(konst(0))),
                    assign(
                        Place::local(3),
                        Rvalue::Ref {
                            mutable: true,
                            place: Place { local: 1, projections: vec![Projection::Deref] },
                        },
                    ),
                ],
                call(vec![Operand::Move(Place::local(3))], Place::local(4), 3, Some(INV)),
            ),
            blk(2, vec![assign(self_field(1, 2), Rvalue::Use(konst(0)))], goto(4)),
            blk(3, vec![], goto(4)),
            blk(4, vec![], Terminator::Return),
        ],
    );
    let inventory: HashSet<CalleeIdentity> = [INV].into_iter().collect();
    let rows = rows_with(&f, &[p_tinv()], &inventory);
    // TINV-9(a): bb4 joins bb2 and bb3, so its R point is split, and each part's post-call
    // facts are dominance-checked against ITS predecessor: the call's target bb3 dominates
    // the via-bb3 part (which then holds), never the via-bb2 part.
    let parts: Vec<_> =
        rows.iter().filter(|(k, _)| k.point == TypeInvariantPoint::Return).collect();
    assert_eq!(parts.iter().map(|(k, _)| k.edge).collect::<Vec<_>>(), vec![Some(2), Some(3)]);
    let body = |vc: &VerificationCondition| vc.obligation.as_ref().expect("record").body.clone();
    let via2 = body(&parts[0].1);
    // The Goto edge's guard slot is `true`; nothing else precedes the negated core.
    assert!(
        matches!(&via2, Formula::And(h) if h.len() == 2 && h[0] == Formula::Bool(true)
            && matches!(h[1], Formula::Not(_))),
        "no post-call fact may reach the bb2 edge: {via2:?}"
    );
    let via3 = body(&parts[1].1);
    assert!(
        matches!(&via3, Formula::And(h) if h.len() >= 3),
        "the bb3 edge has the fact: {via3:?}"
    );
    assert_eq!(parts[1].1.type_invariant_situatedness_refusal(), None);
    assert_unsat(&parts[1].1);
}

// ---------------------------------------------------------------------------------------
// (viii) budget, (ix) one-shot, refusals
// ---------------------------------------------------------------------------------------

#[test]
fn a_step_budget_trip_refuses_the_body_as_truncated() {
    let got = plan_run(&bump(Bump::Guarded), &[p_tinv()], &HashSet::new(), &|_| true, 1);
    assert!(matches!(got, Err(TinvObligationRefusal::Truncated)), "{got:?}");
}

#[test]
fn a_second_walk_under_the_same_request_emits_nothing() {
    let f = bump(Bump::Guarded);
    let req = Rc::new(rows_request_for(&f));
    let _g = enter_tinv_rows(Rc::clone(&req));
    let tinv = |rows: Vec<(BlockId, VerificationCondition)>| {
        rows.into_iter().filter(|(_, vc)| matches!(vc.kind, VcKind::TypeInvariant { .. })).count()
    };
    let first =
        tinv(super::safety::generate_v2_safety_vcs_impl_with_origins_checked(&f, None).rows);
    assert_eq!(first, 1);
    let second =
        tinv(super::safety::generate_v2_safety_vcs_impl_with_origins_checked(&f, None).rows);
    assert_eq!(second, 0);
    assert!(req.state.borrow().reused);
}

#[test]
fn duplicate_types_refuse_and_a_refused_type_is_reported_not_silent() {
    let got =
        plan_run(&bump(Bump::Guarded), &[p_tinv(), p_tinv()], &HashSet::new(), &|_| true, u64::MAX);
    assert!(matches!(got, Err(TinvObligationRefusal::DuplicateDefPath(_))), "{got:?}");
    // A type whose enumeration refuses (a tail call) lands in `refused`, with no rows.
    let mut f = bump(Bump::Guarded);
    f.body.blocks[3].terminator = Terminator::TailCall {
        func: "c::g".into(),
        args: Vec::new(),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
    };
    let got = plan_run(&f, &[p_tinv()], &HashSet::new(), &|_| true, u64::MAX).expect("body result");
    assert!(got.rows.is_empty());
    assert_eq!(got.refused.len(), 1);
}

// ---------------------------------------------------------------------------------------
// The TYPE-RANGE battery on TINV rows (2026-10-06): E rows over integer PARAMETERS
// ---------------------------------------------------------------------------------------

/// `fn new(a: T, b: T) -> Q { Q { x: <ops[0]>, y: <ops[1]> } }` on a two-field `Q` of
/// field type `t`, where `ops` names the parameters (`_1`, `_2`) or constants.
fn param_ctor(name: &str, ty: &str, t: &Ty, ops: Vec<Operand>) -> VerifiableFunction {
    let q = adt(ty, &[("x", t.clone()), ("y", t.clone())]);
    func(
        name,
        vec![(q, None), (t.clone(), Some("a")), (t.clone(), Some("b"))],
        2,
        vec![blk(
            0,
            vec![assign(
                Place::local(0),
                Rvalue::Aggregate(
                    AggregateKind::Adt {
                        name: ty.into(),
                        variant: 0,
                        active_field: None,
                        args: None,
                    },
                    ops,
                ),
            )],
            Terminator::Return,
        )],
    )
}

fn q_tinv(ty: &str, t: &Ty, formula: Formula) -> TinvType {
    TinvType {
        def_path: ty.into(),
        fields: vec![("x".to_string(), t.clone()), ("y".to_string(), t.clone())],
        conjuncts: vec![CandidateConjunct { id: 0, formula }],
    }
}

/// `f` reads the variable `name` itself (bare or SSA-versioned), not a longer name.
fn names_exactly(f: &Formula, name: &str) -> bool {
    let mut hit = false;
    f.visit(&mut |n| {
        if let Formula::Var(v, _) = n
            && v.split('#').next() == Some(name)
        {
            hit = true;
        }
    });
    hit
}

fn qv(i: usize) -> Box<Formula> {
    Box::new(field_var(FieldTerm::Value(i)))
}

/// The E row of `new(n: u64) -> Q { Q { x: 0, y: n } }` against `x <= y` (core
/// `Not(0 <= n)`): the parameter range `0 <= n <= u64::MAX` is a battery fact recorded in
/// the obligation, so the row is SITUATED (the core's `n` is bound by a hypothesis) and
/// UNSAT. Before the TINV battery class the row carried `0 <= len` facts only, named no
/// `n`, and the situatedness gate refused it.
#[test]
fn an_establish_row_over_an_unsigned_parameter_is_situated_by_its_type_range_and_unsat() {
    let t = u64_ty();
    let f = param_ctor("new_q", "c::Q", &t, vec![konst(0), Operand::Copy(Place::local(2))]);
    let rows = rows_of(&f, &[q_tinv("c::Q", &t, Formula::Le(qv(0), qv(1)))]);
    let e = only(&rows, TypeInvariantPoint::Establish);
    assert_eq!(e.type_invariant_situatedness_refusal(), None, "{:?}", e.formula);
    let record = e.obligation.as_ref().expect("record");
    assert!(
        record.wrappers.iter().any(|w| match w {
            trust_types::ObligationWrapper::ConjoinFactsLast { facts } => {
                facts.iter().any(|f| names_exactly(f, "b"))
            }
            trust_types::ObligationWrapper::PathGuardOr { .. } => false,
        }),
        "the parameter range is a recorded wrapper fact: {:?}",
        record.wrappers
    );
    assert_unsat(e);
}

/// The range facts must not hide a real violation: `Q { x: n, y: 0 }` against `x <= y`
/// (core `Not(n <= 0)`) is situated and SAT (`n = 1` is a `u64`).
#[test]
fn an_establish_row_that_violates_through_an_unsigned_parameter_stays_sat() {
    let t = u64_ty();
    let f = param_ctor("bad_q", "c::Q", &t, vec![Operand::Copy(Place::local(1)), konst(0)]);
    let rows = rows_of(&f, &[q_tinv("c::Q", &t, Formula::Le(qv(0), qv(1)))]);
    let e = only(&rows, TypeInvariantPoint::Establish);
    assert_eq!(e.type_invariant_situatedness_refusal(), None, "{:?}", e.formula);
    assert_sat(e);
}

/// Signed: `Q { x: a, y: b }` on `i64` fields against `0 <= x` is situated and SAT
/// (`a = -1` is an `i64`): the signed range is `[i64::MIN, i64::MAX]`, not `0 <= a`.
#[test]
fn an_establish_row_over_a_signed_parameter_is_situated_and_sat() {
    let t = Ty::Int { width: 64, signed: true };
    let f = param_ctor(
        "new_s",
        "c::Qs",
        &t,
        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
    );
    let rows = rows_of(&f, &[q_tinv("c::Qs", &t, Formula::Le(Box::new(Formula::Int(0)), qv(0)))]);
    let e = only(&rows, TypeInvariantPoint::Establish);
    assert_eq!(e.type_invariant_situatedness_refusal(), None, "{:?}", e.formula);
    assert_sat(e);
}

/// `fn f(&mut self) { self.i = 7; self.k += 1 }` against `i <= n`: the window is open at
/// the overflow assert of `k + 1`, whose U row carries the assert's FAILURE condition.
/// The row is a real violation (`n = 0`), so with the battery's range facts (here on
/// `self*.0`, both versions) it must stay SAT.
///
/// MEASURED (2026-10-06): the failure condition is the free flag `_2.1#s0_1` — no fact
/// ties it to `k + 1` on this row — so the battery's checked-op exclusion (`_2.0`) is not
/// load-bearing on this shape: the test also passes with the exclusion removed. The
/// exclusion stays as the fail-closed precaution `RangeBatteryClass::TypeInvariant`
/// documents; this test is the rail that the battery does not discharge a real U
/// violation.
#[test]
fn an_unwind_row_at_an_overflow_assert_that_violates_stays_sat_under_the_battery() {
    let locals = vec![
        (Ty::Unit, None),
        (mut_ref(p_ty()), Some("self")),
        (Ty::Tuple(vec![u64_ty(), Ty::Bool]), None),
    ];
    let f = func(
        "set_then_bump_k",
        locals,
        1,
        vec![
            blk(
                0,
                vec![
                    assign(self_field(1, 0), Rvalue::Use(konst(7))),
                    assign(
                        Place::local(2),
                        Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(self_field(1, 2)),
                            konst(1),
                        ),
                    ),
                ],
                overflow_assert(2, 1),
            ),
            blk(
                1,
                vec![assign(self_field(1, 2), Rvalue::Use(Operand::Move(field(2, 0))))],
                Terminator::Return,
            ),
        ],
    );
    let rows = rows_of(&f, &[p_tinv()]);
    let u = only(&rows, TypeInvariantPoint::Unwind);
    assert_eq!(u.type_invariant_situatedness_refusal(), None, "{:?}", u.formula);
    assert_sat(u);
}

/// `fn reset(&mut self, m: u64) { self.i = 0; self.n = m; g(&mut *self) }` against
/// `i <= n` (`tail` adds the call; without it the body returns). The C row before the
/// call and the R row read the PARAMETER `m` through σ (`n := m`), core `Not(0 <= m)`:
/// both are situated by `m`'s type range and UNSAT. The same gap as the E row: before
/// the TINV battery class neither row carried a hypothesis naming `m`.
#[test]
fn call_and_return_rows_over_an_integer_parameter_are_situated_and_unsat() {
    let body = |with_call: bool| {
        let writes = vec![
            assign(self_field(1, 0), Rvalue::Use(konst(0))),
            assign(self_field(1, 1), Rvalue::Use(Operand::Copy(Place::local(2)))),
        ];
        let mut locals =
            vec![(Ty::Unit, None), (mut_ref(p_ty()), Some("self")), (u64_ty(), Some("m"))];
        if !with_call {
            return func("reset_ret", locals, 2, vec![blk(0, writes, Terminator::Return)]);
        }
        locals.push((mut_ref(p_ty()), None));
        locals.push((Ty::Unit, None));
        let mut stmts = writes;
        stmts.push(assign(
            Place::local(3),
            Rvalue::Ref {
                mutable: true,
                place: Place { local: 1, projections: vec![Projection::Deref] },
            },
        ));
        func(
            "reset_call",
            locals,
            2,
            vec![
                blk(0, stmts, call(vec![Operand::Move(Place::local(3))], Place::local(4), 1, None)),
                blk(1, vec![], Terminator::Return),
            ],
        )
    };
    let rows = rows_of(&body(false), &[p_tinv()]);
    let r = only(&rows, TypeInvariantPoint::Return);
    assert_eq!(r.type_invariant_situatedness_refusal(), None, "{:?}", r.formula);
    assert_unsat(r);
    let rows = rows_of(&body(true), &[p_tinv()]);
    let c = only(&rows, TypeInvariantPoint::Call);
    assert_eq!(c.type_invariant_situatedness_refusal(), None, "{:?}", c.formula);
    assert_unsat(c);
}

// ---------------------------------------------------------------------------------------
// Measurement: the real `peek` body of P1 (the Some-arm lemma design, diagnosis item 7)
// ---------------------------------------------------------------------------------------

#[path = "tinv_peek_measure_tests.rs"]
mod tinv_peek_measure_tests;
