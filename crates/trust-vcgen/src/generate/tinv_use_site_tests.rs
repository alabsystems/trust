//! TINV step 10.3: the use-site facts CONJOINED into real rows of the safety walk
//! (`generate::type_invariant_facts::conjoin_tinv_facts_at_point_recorded`, wired at the
//! user-`requires` conjoin of `safety.rs`), end to end through `generate_vcs_with_context`
//! and the in-process ay router.
//!
//! The use set is built by its only constructor, `TinvUseSet::from_outcome`, over a
//! `TinvOutcome` holding a test certificate (`TypeInvariantCertificate::for_test`): what a
//! use site may assume is a function of the outcome alone, so the certificate's own rows
//! are irrelevant here (the mint is tested in `type_invariant/houdini_tests.rs`).
//!
//! Every test pins a ROW verdict: a use-site fact must discharge exactly the rows its
//! premise covers, and never one where the program changed what the fact talks about.

use std::sync::Arc;

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, CalleeIdentity, Formula, LocalDecl, Operand, Place,
    Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, UnOp, UnwindEdge, VcKind,
    VerifiableBody, VerifiableFunction, VerificationCondition, VerificationResult,
};

use crate::type_invariant::houdini::{TinvOutcome, TypeInvariantCertificate};
use crate::type_invariant::{
    CandidateConjunct, FieldTerm, TinvAssumedRow, TinvType, TinvUseSet, field_var,
};

// ---------------------------------------------------------------------------------------
// Types and the use set
// ---------------------------------------------------------------------------------------

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn u8_ty() -> Ty {
    Ty::Int { width: 8, signed: false }
}

fn slice_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(u8_ty()) }) }
}

fn shared(t: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(t) }
}

fn mutable(t: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(t) }
}

const P: &str = "c::P";

fn p_fields() -> Vec<(String, Ty)> {
    vec![("b".into(), slice_ref()), ("i".into(), u64_ty())]
}

/// `struct P<'a> { b: &'a [u8], i: u64 }`.
fn p_ty() -> Ty {
    Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: P.into(),
        fields: p_fields().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `I(P) = i < len(b)` (conjunct 0).
fn p_tinv() -> TinvType {
    TinvType {
        def_path: P.into(),
        fields: p_fields(),
        conjuncts: vec![CandidateConjunct {
            id: 0,
            formula: Formula::Lt(
                Box::new(field_var(FieldTerm::Value(1))),
                Box::new(field_var(FieldTerm::Len(0))),
            ),
        }],
    }
}

/// The inventory callee every post-call test calls.
const DOWN: CalleeIdentity =
    CalleeIdentity { stable_crate_id: 1, def_index: 41, substs_digest: [0, 0] };

fn use_set(checked: &[&str]) -> Arc<TinvUseSet> {
    let t = p_tinv();
    let out = TinvOutcome::<()> {
        certificates: [(t.def_path.clone(), TypeInvariantCertificate::for_test(&t))]
            .into_iter()
            .collect(),
        inventory: [DOWN].into_iter().collect(),
        checked_bodies: checked.iter().map(|s| s.to_string()).collect(),
        ..TinvOutcome::default()
    };
    Arc::new(TinvUseSet::from_outcome(&out, |_| true).expect("use set"))
}

fn tag0(set: &TinvUseSet) -> String {
    set.tag_for(P, 0).expect("tag").to_owned()
}

// ---------------------------------------------------------------------------------------
// Bodies
// ---------------------------------------------------------------------------------------

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

fn proj(local: usize, projections: Vec<Projection>) -> Place {
    Place { local, projections }
}

fn call(
    callee: &str,
    args: Vec<Operand>,
    dest: Place,
    target: usize,
    identity: Option<CalleeIdentity>,
    unwind: UnwindEdge,
) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest,
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind,
        callee_identity: identity,
        callee_key: None,
    }
}

/// The root's projections down to `P`: `[]` for a by-value local, `[Deref]` for a reference.
fn root_proj(by_ref: bool) -> Vec<Projection> {
    if by_ref { vec![Projection::Deref] } else { vec![] }
}

/// The statements of `root.b[root.i]`'s bounds check, reading into `_idx`, `_len`, `_ok`:
/// `_idx = copy root.1; _len = PtrMetadata(copy root.0); _ok = Lt(copy _idx, copy _len)`.
fn index_check(
    root_local: usize,
    by_ref: bool,
    idx: usize,
    len: usize,
    ok: usize,
) -> Vec<Statement> {
    let field = |f: usize| {
        let mut p = root_proj(by_ref);
        p.push(Projection::Field(f));
        p
    };
    vec![
        assign(Place::local(idx), Rvalue::Use(Operand::Copy(proj(root_local, field(1))))),
        // rustc's `PtrMetadata(copy root.0)`: the length of the `&[u8]` field.
        assign(
            Place::local(len),
            Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(proj(root_local, field(0)))),
        ),
        assign(
            Place::local(ok),
            Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::local(idx)),
                Operand::Copy(Place::local(len)),
            ),
        ),
    ]
}

fn bounds_assert(ok: usize, target: usize) -> Terminator {
    Terminator::Assert {
        unwind: UnwindEdge::Unreachable,
        cond: Operand::Move(Place::local(ok)),
        expected: true,
        msg: AssertMessage::BoundsCheck,
        target: BlockId(target),
        span: SourceSpan::default(),
    }
}

/// The read `_0 = copy (*root.0)[_idx]`.
fn index_read(root_local: usize, by_ref: bool, idx: usize) -> Statement {
    let mut p = root_proj(by_ref);
    p.extend([Projection::Field(0), Projection::Deref, Projection::Index(idx)]);
    assign(Place::local(0), Rvalue::Use(Operand::Copy(proj(root_local, p))))
}

/// The common locals of an index body: `_0: u8`, `_1: <param>`, then `extra`, then
/// `_idx, _len, _ok` (returned as their indices).
/// A body's locals, `(type, name)` in index order.
type Locals = Vec<(Ty, Option<&'static str>)>;

fn index_locals(param: Ty, extra: Locals) -> (Locals, usize, usize, usize) {
    let mut locals = vec![(u8_ty(), None), (param, Some("self"))];
    locals.extend(extra);
    let idx = locals.len();
    locals.extend([(u64_ty(), None), (u64_ty(), None), (Ty::Bool, None)]);
    (locals, idx, idx + 1, idx + 2)
}

/// `fn at(&self) -> u8 { self.b[self.i] }` (`by_ref`), or by value `fn at(self) -> u8`.
fn at(name: &str, by_ref: bool) -> VerifiableFunction {
    let param = if by_ref { shared(p_ty()) } else { p_ty() };
    let (locals, idx, len, ok) = index_locals(param, vec![]);
    func(
        name,
        locals,
        1,
        vec![
            blk(0, index_check(1, by_ref, idx, len, ok), bounds_assert(ok, 1)),
            blk(1, vec![index_read(1, by_ref, idx)], Terminator::Return),
        ],
    )
}

// ---------------------------------------------------------------------------------------
// Generation and the solver
// ---------------------------------------------------------------------------------------

fn context_for(f: &VerifiableFunction, set: Option<Arc<TinvUseSet>>) -> crate::VcgenContext {
    let summaries = crate::CalleeSummaryContext::default().with_type_invariants(set);
    crate::VcgenContext::for_function(f.def_path.clone()).with_callee_summaries(summaries)
}

/// Generate `f`'s VCs under `set` installed (or none), INSIDE a recording scope for `f`
/// (the generation whose rows a caller consumes), returning the rows and the record.
fn generate(
    f: &VerifiableFunction,
    set: Option<Arc<TinvUseSet>>,
) -> (Vec<VerificationCondition>, Vec<TinvAssumedRow>) {
    let context = context_for(f, set);
    let (vcs, record) = crate::type_invariant::with_tinv_assumed_rows_scope(f, || {
        super::generate_vcs_with_context(f, &context)
    });
    assert!(!record.conflicting_sets);
    (vcs, record.rows)
}

/// The tags a row's FORMULA carries.
fn formula_tags(vc: &VerificationCondition) -> std::collections::BTreeSet<String> {
    match vc.type_invariant_tags() {
        trust_types::TinvTagScan::None => Default::default(),
        trust_types::TinvTagScan::Tags(tags) => tags,
        trust_types::TinvTagScan::Unbounded => panic!("unbounded tag scan"),
    }
}

/// THE TAG-SEPARATION TRIPWIRE, on one generation: per row key `(kind, location)`, the
/// multiset of the recorded tag sets EQUALS the multiset of the non-empty
/// formula tag sets of the rows with that key. So every row that received a fact still
/// carries exactly its tags, and no row carries a tag nothing recorded. (Two rows may share
/// a key; the compiler then compares each row with the key's UNION, which refuses the
/// untagged sibling — a precision cost, never a lost disclosure.) A `TypeInvariant` row
/// never carries a tag.
fn assert_channels_agree(vcs: &[VerificationCondition], rows: &[TinvAssumedRow]) {
    let key = |kind: &VcKind, location: &SourceSpan| format!("{kind:?}@{location:?}");
    let mut recorded: std::collections::BTreeMap<String, Vec<Vec<String>>> = Default::default();
    for row in rows {
        assert!(!row.tags.is_empty(), "a record with no tag: {row:?}");
        recorded
            .entry(key(&row.kind, &row.location))
            .or_default()
            .push(row.tags.iter().cloned().collect());
    }
    let mut carried: std::collections::BTreeMap<String, Vec<Vec<String>>> = Default::default();
    for vc in vcs {
        let tags = formula_tags(vc);
        if matches!(vc.kind, VcKind::TypeInvariant { .. }) {
            assert!(tags.is_empty(), "a TypeInvariant row carries a use-site tag");
        }
        if !tags.is_empty() {
            carried
                .entry(key(&vc.kind, &vc.location))
                .or_default()
                .push(tags.into_iter().collect());
        }
    }
    for list in recorded.values_mut().chain(carried.values_mut()) {
        list.sort();
    }
    assert_eq!(recorded, carried, "the formula tags and the generation's record disagree");
}

/// Every SliceBoundsCheck/IndexOutOfBounds row of `vcs`.
fn index_rows(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    vcs.iter()
        .filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds))
        .collect()
}

fn solve(vc: &VerificationCondition) -> VerificationResult {
    let vc = vc.clone();
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

fn proved(vc: &VerificationCondition) -> bool {
    matches!(solve(vc), VerificationResult::Proved { .. })
}

fn refuted(vc: &VerificationCondition) -> bool {
    matches!(solve(vc), VerificationResult::Failed { .. })
}

/// Generate `f` under `set`, check the two channels agree, and report each index row's
/// verdict (in row order), whether every one proved, the tags the rows carry, and the
/// records.
struct Run {
    verdicts: Vec<bool>,
    all_proved: bool,
    tags: Vec<String>,
    rows: Vec<TinvAssumedRow>,
}

/// The use set changed NO index row's verdict: every row the set's facts reach proves
/// exactly when it proves with no set (a row discharged by its own guard proves either way).
fn assert_no_row_gained(f: &VerifiableFunction, set: Arc<TinvUseSet>, what: &str) -> Run {
    let with = run(f, Some(set));
    let without = run(f, None);
    assert_eq!(with.verdicts, without.verdicts, "{what}: a use-site fact discharged a row");
    with
}

fn run(f: &VerifiableFunction, set: Option<Arc<TinvUseSet>>) -> Run {
    let (vcs, rows) = generate(f, set);
    assert_channels_agree(&vcs, &rows);
    let index = index_rows(&vcs);
    assert!(!index.is_empty(), "no index row: {vcs:#?}");
    let mut tags = std::collections::BTreeSet::new();
    let mut verdicts = Vec::new();
    for vc in index {
        tags.extend(formula_tags(vc));
        let ok = proved(vc);
        if !ok {
            assert!(refuted(vc), "neither proved nor refuted: {vc:?}");
        }
        verdicts.push(ok);
    }
    let all_proved = verdicts.iter().all(|ok| *ok);
    Run { verdicts, all_proved, tags: tags.into_iter().collect(), rows }
}

// ---------------------------------------------------------------------------------------
// 10.3-LEN, end to end (landed FIRST: if a length name were not re-versioned, an entry
// fact over it would bind the post-change length and every entry fact would be unsound)
// ---------------------------------------------------------------------------------------

/// `fn reseat(mut self: P, o: &[u8]) -> u8 { self.b = o; self.b[self.i] }`: the store
/// re-versions the field's `__slice_len`, so the entry fact `i < len(b)` binds the OLD
/// length and no index row is discharged. Control: without the store the row proves.
#[test]
fn len_a_store_to_the_slice_field_reversions_its_length_at_the_use_site() {
    let build = |store: bool| {
        let (locals, idx, len, ok) = index_locals(p_ty(), vec![(slice_ref(), Some("o"))]);
        let mut bb0 = Vec::new();
        if store {
            bb0.push(assign(
                proj(1, vec![Projection::Field(0)]),
                Rvalue::Use(Operand::Copy(Place::local(2))),
            ));
        }
        bb0.extend(index_check(1, false, idx, len, ok));
        func(
            if store { "reseat" } else { "keep" },
            locals,
            2,
            vec![
                blk(0, bb0, bounds_assert(ok, 1)),
                blk(1, vec![index_read(1, false, idx)], Terminator::Return),
            ],
        )
    };
    let keep = run(&build(false), Some(use_set(&["c::keep"])));
    assert!(keep.all_proved, "control: the entry fact discharges the unchanged row");
    assert!(!run(&build(false), None).all_proved, "control: without the set it does not");
    assert_eq!(keep.tags.len(), 1);
    assert_no_row_gained(&build(true), use_set(&["c::reseat"]), "reseat");
}

/// `fn shrink(mut s: S) { Vec::clear(&mut s.v); s.v[s.k] }` and the same with `push`: the
/// `&mut` call on the `Vec` field re-versions its length, so no index row is discharged.
/// (No positive control here: the `Vec` `Index::index` row reads its length off the
/// receiver temp, which nothing ties to the field's length name — a precision gap of the
/// index model, not of this lane. The slice test above carries the control; the oracle
/// half of the `Vec` cases is `tinv_len_versioning_tests`.)
#[test]
fn len_a_mut_call_on_the_vec_field_never_lets_the_entry_fact_discharge_the_index() {
    let vec_ty = Ty::Seq { elem: Box::new(u8_ty()), drop_auth: None };
    let s_fields = vec![("v".to_string(), vec_ty.clone()), ("k".to_string(), u64_ty())];
    let s_ty = Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: "c::S".into(),
        fields: s_fields.clone().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let t = TinvType {
        def_path: "c::S".into(),
        fields: s_fields,
        conjuncts: vec![CandidateConjunct {
            id: 0,
            formula: Formula::Lt(
                Box::new(field_var(FieldTerm::Value(1))),
                Box::new(field_var(FieldTerm::Len(0))),
            ),
        }],
    };
    let set_for = |body: &str| {
        let out = TinvOutcome::<()> {
            certificates: [(t.def_path.clone(), TypeInvariantCertificate::for_test(&t))]
                .into_iter()
                .collect(),
            inventory: [DOWN].into_iter().collect(),
            checked_bodies: [body.to_string()].into_iter().collect(),
            ..TinvOutcome::default()
        };
        Arc::new(TinvUseSet::from_outcome(&out, |_| true).expect("use set"))
    };
    let index = "<alloc::vec::Vec<u8> as core::ops::index::Index<usize>>::index";
    // bb0: [_2 = &mut s.0] <mutator>(move _2, extra) -> bb1;
    // bb1: [_4 = &s.0; _5 = copy s.1] index(move _4, move _5) -> bb2; bb2: return
    let build = |name: &str, callee: &str, extra: Vec<Operand>| {
        let vref = |m: bool| Ty::Ref { mutable: m, inner: Box::new(vec_ty.clone()) };
        let field0 = proj(1, vec![Projection::Field(0)]);
        let mut args = vec![Operand::Move(Place::local(2))];
        args.extend(extra);
        func(
            name,
            vec![
                (Ty::Unit, None),
                (s_ty.clone(), Some("s")),
                (vref(true), None),
                (Ty::Unit, None),
                (vref(false), None),
                (u64_ty(), None),
                (Ty::Ref { mutable: false, inner: Box::new(u8_ty()) }, None),
            ],
            1,
            vec![
                blk(
                    0,
                    vec![assign(
                        Place::local(2),
                        Rvalue::Ref { mutable: true, place: field0.clone() },
                    )],
                    call(callee, args, Place::local(3), 1, None, UnwindEdge::Continue),
                ),
                blk(
                    1,
                    vec![
                        assign(Place::local(4), Rvalue::Ref { mutable: false, place: field0 }),
                        assign(
                            Place::local(5),
                            Rvalue::Use(Operand::Copy(proj(1, vec![Projection::Field(1)]))),
                        ),
                    ],
                    call(
                        index,
                        vec![Operand::Move(Place::local(4)), Operand::Move(Place::local(5))],
                        Place::local(6),
                        2,
                        None,
                        UnwindEdge::Continue,
                    ),
                ),
                blk(2, vec![], Terminator::Return),
            ],
        )
    };
    let x = Operand::Constant(trust_types::ConstValue::Uint(7, 8));
    for (name, callee, extra) in [
        ("shrink", "alloc::vec::Vec::<u8>::clear", vec![]),
        ("grow", "alloc::vec::Vec::<u8>::push", vec![x]),
    ] {
        let f = build(name, callee, extra);
        assert_no_row_gained(&f, set_for(&f.def_path), name);
    }
}

// ---------------------------------------------------------------------------------------
// The positive case and its controls
// ---------------------------------------------------------------------------------------

/// `fn at(&self) -> u8 { self.b[self.i] }` and its by-value twin prove under the use set,
/// with exactly one tag, and the installation record names the same tag. Without a use set,
/// or with `at` outside `checked_bodies`, there is no fact and the row is refuted.
#[test]
fn an_entry_fact_proves_the_index_row_with_one_disclosed_tag() {
    for by_ref in [true, false] {
        let f = at("at", by_ref);
        let set = use_set(&["c::at"]);
        let out = run(&f, Some(Arc::clone(&set)));
        assert!(out.all_proved, "by_ref={by_ref}: the entry fact must discharge the row");
        assert_eq!(out.tags, vec![tag0(&set)]);
        assert_eq!(out.rows.len(), 1);
        assert_eq!(out.rows[0].def_path, "c::at");
        assert_eq!(out.rows[0].kind, VcKind::SliceBoundsCheck);
        assert_eq!(out.rows[0].tags.iter().cloned().collect::<Vec<_>>(), out.tags);
        // The fact is the row's SECOND recorded `ConjoinFactsLast`, after the requires one.
        let (vcs, _) = generate(&f, Some(Arc::clone(&set)));
        let row = index_rows(&vcs).into_iter().find(|vc| !formula_tags(vc).is_empty()).unwrap();
        let ob = row.obligation.as_ref().expect("an obligation record");
        let tagged_wrapper = ob.wrappers.iter().position(|w| match w {
            trust_types::ObligationWrapper::ConjoinFactsLast { facts } => facts.iter().any(|f| {
                let mut hit = false;
                f.visit(&mut |n| hit |= matches!(n, Formula::Var(v, _) if *v == out.tags[0]));
                hit
            }),
            _ => false,
        });
        assert!(tagged_wrapper.is_some_and(|i| i >= 1), "{:?}", ob.wrappers);

        // Controls: no set; a set whose induction never walked `at`.
        let none = run(&f, None);
        assert!(!none.all_proved && none.tags.is_empty() && none.rows.is_empty());
        let other = run(&f, Some(use_set(&["c::other"])));
        assert!(!other.all_proved && other.tags.is_empty() && other.rows.is_empty());
    }
}

/// With no use set installed the generation is BYTE-IDENTICAL to an empty context's (the
/// state of every real compile until step 10.5), and so is one under a set that gives the
/// body nothing.
#[test]
fn no_installed_set_leaves_every_row_byte_identical() {
    let f = at("at", true);
    let plain = super::generate_vcs(&f);
    let (with_context, rows) = generate(&f, None);
    assert!(rows.is_empty());
    assert_eq!(format!("{plain:?}"), format!("{with_context:?}"));
    let (other, rows) = generate(&f, Some(use_set(&["c::other"])));
    assert!(rows.is_empty());
    assert_eq!(format!("{plain:?}"), format!("{other:?}"));
}

// ---------------------------------------------------------------------------------------
// D2 alias, rail 23, cleanup
// ---------------------------------------------------------------------------------------

/// `let r = &mut self.i; *r = v; self.b[self.i]` (the D2 alias shape the census admits,
/// `tests/fixtures/tinv_alias_write_fx.rs`): the write through the alias re-versions
/// `self.i`, so the entry fact discharges no index row. Both a by-value `self` and, with
/// the `&mut` entry channel forced on, a `&mut self` pointee. Control: no write, proved.
#[test]
fn d2_a_write_through_a_field_alias_is_not_bound_by_the_entry_fact() {
    let _on = super::type_invariant_facts::override_mut_entry_facts(true);
    for by_ref in [false, true] {
        let param = if by_ref { mutable(p_ty()) } else { p_ty() };
        let build = |name: &str, alias_write: bool| {
            let (locals, idx, len, ok) = index_locals(
                param.clone(),
                vec![(u64_ty(), Some("v")), (mutable(u64_ty()), Some("r"))],
            );
            let mut i_field = root_proj(by_ref);
            i_field.push(Projection::Field(1));
            let mut bb0 = Vec::new();
            if alias_write {
                bb0.push(assign(
                    Place::local(3),
                    Rvalue::Ref { mutable: true, place: proj(1, i_field.clone()) },
                ));
                bb0.push(assign(
                    proj(3, vec![Projection::Deref]),
                    Rvalue::Use(Operand::Copy(Place::local(2))),
                ));
            }
            bb0.extend(index_check(1, by_ref, idx, len, ok));
            func(
                name,
                locals,
                2,
                vec![
                    blk(0, bb0, bounds_assert(ok, 1)),
                    blk(1, vec![index_read(1, by_ref, idx)], Terminator::Return),
                ],
            )
        };
        let control = run(&build("plain", false), Some(use_set(&["c::plain"])));
        let baseline = run(&build("plain", false), None);
        assert!(control.all_proved && !baseline.all_proved, "by_ref={by_ref}: control");
        assert!(!control.tags.is_empty());
        let aliased = build("set", true);
        assert_no_row_gained(&aliased, use_set(&["c::set"]), "the alias write");
    }
}

/// RAIL 23 at the use site, on the stage-1 extraction of
/// `fn rebind(&mut self) -> u8 { let a = self.v[self.k]; self.k = self.v.len(); a ^ self.v[self.k] }`
/// (`tests/fixtures/tinv_mut_pointee_entry_rename_mir.json`), with the `&mut` entry channel
/// forced on (the gate `TINV_MUT_ENTRY_FACTS` flips on step 10.6): the entry fact reaches the
/// pre-write row (bb0, line 4) and no tagged instance names the post-write `k`, and every
/// row reading the post-write `k` stays refuted.
///
/// MEASURED (step 10.3): the pre-write row is tagged but NOT discharged — the real `Vec`
/// `Index::index` row reads its length off the receiver temp `_4`, which nothing ties to
/// the field's length name `self*.0` (an index-model precision gap, outside this lane). The
/// plan expected it discharged; the soundness half of the rail holds.
#[test]
fn rail_23_the_mut_entry_fact_never_binds_the_post_write_read() {
    let _on = super::type_invariant_facts::override_mut_entry_facts(true);
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/tinv_mut_pointee_entry_rename_mir.json"
    );
    let f: VerifiableFunction =
        serde_json::from_str(&std::fs::read_to_string(path).expect("fixture")).expect("json");
    let Some(Ty::Ref { inner, .. }) = f.body.locals.get(1).map(|l| l.ty.clone()) else {
        panic!("rebind's self is a reference")
    };
    let Ty::Adt { name, fields, .. } = *inner else { panic!("S is an ADT") };
    let t = TinvType {
        def_path: name.to_string(),
        fields: fields.iter().cloned().collect(),
        conjuncts: vec![CandidateConjunct {
            id: 0,
            formula: Formula::Lt(
                Box::new(field_var(FieldTerm::Value(1))),
                Box::new(field_var(FieldTerm::Len(0))),
            ),
        }],
    };
    let out = TinvOutcome::<()> {
        certificates: [(t.def_path.clone(), TypeInvariantCertificate::for_test(&t))]
            .into_iter()
            .collect(),
        checked_bodies: [f.def_path.clone()].into_iter().collect(),
        ..TinvOutcome::default()
    };
    let set = Arc::new(TinvUseSet::from_outcome(&out, |_| true).expect("use set"));
    let (vcs, rows) = generate(&f, Some(set));
    assert_channels_agree(&vcs, &rows);
    // The pre-write row (line 4) carries the entry fact.
    let rows4: Vec<&VerificationCondition> =
        index_rows(&vcs).into_iter().filter(|vc| vc.location.line_start == 4).collect();
    assert!(rows4.iter().any(|vc| !formula_tags(vc).is_empty()), "{rows4:#?}");
    // No tagged instance anywhere names a post-write version of `k`.
    let sv = super::stmt_versions_for(&f);
    let post = sv.version_token_at(&f, BlockId(2), 2, "self*.1").expect("re-versioned");
    let post_name = format!("self*.1#{post}");
    let is_tag = |n: &Formula| matches!(n, Formula::Var(v, _) if trust_types::is_type_invariant_assume_tag(v));
    for vc in &vcs {
        let Some(ob) = vc.obligation.as_ref() else { continue };
        for w in &ob.wrappers {
            let trust_types::ObligationWrapper::ConjoinFactsLast { facts } = w else { continue };
            for fact in facts {
                let (mut tagged, mut meets) = (false, false);
                fact.visit(&mut |n| {
                    tagged |= is_tag(n);
                    meets |= matches!(n, Formula::Var(v, _) if *v == post_name);
                });
                assert!(
                    !(tagged && meets),
                    "an entry instance names the post-write read: {fact:?}"
                );
            }
        }
    }
    // Every index row reading the post-write `k` is refuted.
    for vc in index_rows(&vcs) {
        let mut reads_post = false;
        vc.formula.visit(&mut |n| reads_post |= matches!(n, Formula::Var(v, _) if *v == post_name));
        if reads_post {
            assert!(refuted(vc), "a post-write row was discharged: {vc:?}");
        }
    }
}

/// A cleanup block reading `self.b[self.i]` after the call it unwinds from.
/// `write`: `self.i = v` before the call. `pass_self`: the call (into the inventory)
/// receives `&mut self`, so it is a post-call point whose target is NOT the cleanup block.
fn cleanup_body(name: &str, write: bool, pass_self: bool) -> VerifiableFunction {
    // bb0: [self.i = v?; _3 = &mut self] down(move _3?) -> bb1, unwind bb2
    // bb1: return; bb2 (cleanup): [idx/len/ok] assert -> bb3; bb3: [read] resume
    let (locals, idx, len, ok) = index_locals(
        p_ty(),
        vec![(u64_ty(), Some("v")), (mutable(p_ty()), None), (Ty::Unit, None)],
    );
    let mut bb0 = Vec::new();
    if write {
        bb0.push(assign(
            proj(1, vec![Projection::Field(1)]),
            Rvalue::Use(Operand::Copy(Place::local(2))),
        ));
    }
    let mut args = Vec::new();
    if pass_self {
        bb0.push(assign(Place::local(3), Rvalue::Ref { mutable: true, place: Place::local(1) }));
        args.push(Operand::Move(Place::local(3)));
    }
    func(
        name,
        locals,
        2,
        vec![
            blk(
                0,
                bb0,
                call(
                    "c::down",
                    args,
                    Place::local(4),
                    1,
                    Some(DOWN),
                    UnwindEdge::Cleanup(BlockId(2)),
                ),
            ),
            blk(1, vec![], Terminator::Return),
            blk(2, index_check(1, false, idx, len, ok), bounds_assert(ok, 3)),
            blk(3, vec![index_read(1, false, idx)], Terminator::Resume),
        ],
    )
}

/// CLEANUP RAIL. (a) The entry fact reaches a cleanup block (control: with no write it
/// discharges the cleanup read), but after a write to `self.i` it does not bind the
/// cleanup read. (b) A post-call fact never attaches in the cleanup block of the call: the
/// call's normal target does not dominate it, so the cleanup read gets no fact at all.
#[test]
fn cleanup_rail_no_fact_binds_a_cleanup_read_after_a_write() {
    let control = cleanup_body("cleanup_ctl", false, false);
    let out = run(&control, Some(use_set(&["c::cleanup_ctl"])));
    assert!(!out.tags.is_empty(), "the entry fact reaches the cleanup block");
    assert!(out.all_proved && !run(&control, None).all_proved, "control");

    let written = cleanup_body("cleanup_w", true, false);
    let out = assert_no_row_gained(&written, use_set(&["c::cleanup_w"]), "the cleanup read");
    assert!(!out.tags.is_empty(), "the entry fact is conjoined and binds nothing");

    let after_call = cleanup_body("cleanup_pc", false, true);
    let out = assert_no_row_gained(&after_call, use_set(&["c::cleanup_pc"]), "post-call cleanup");
    assert!(out.tags.is_empty() && out.rows.is_empty(), "a fact attached in the cleanup block");
}

// ---------------------------------------------------------------------------------------
// Circularity
// ---------------------------------------------------------------------------------------

/// The mint's own rows assume nothing from a use set: `type_invariant_check_vcs` under a
/// context carrying one gives BYTE-IDENTICAL rows, none tagged, and records nothing.
/// (Houdini itself refuses to run under a visible set:
/// `houdini_refuses_every_type_when_a_use_set_is_visible`.)
#[test]
fn circularity_tinv_rows_are_byte_identical_and_untagged_under_a_use_set() {
    use crate::type_invariant::obligations::{BodyTinvPlan, type_invariant_check_vcs};
    let f = post_call("g", Some(DOWN), false, false);
    let types = [p_tinv()];
    let inventory = [DOWN].into_iter().collect();
    let rows_of = || {
        let plan = BodyTinvPlan {
            types: &types,
            facts: None,
            inventory: &inventory,
            models: &crate::type_invariant::unwind::NoExactModels,
            may_run_user_drop: &|_| true,
            step_budget: u64::MAX,
        };
        type_invariant_check_vcs(&f, &plan)
    };
    let plain = format!("{:?}", rows_of());
    let summaries =
        crate::CalleeSummaryContext::default().with_type_invariants(Some(use_set(&["c::g"])));
    let _g = crate::enter_test_callee_summaries(summaries);
    // Even inside a recording scope for the body.
    let (under, record) = crate::type_invariant::with_tinv_assumed_rows_scope(&f, rows_of);
    let record = record.rows;
    assert_eq!(plain, format!("{under:?}"));
    let out = under.expect("the body is walked");
    assert!(!out.rows.is_empty(), "the walk produced rows");
    for (_, vc) in &out.rows {
        assert_eq!(vc.type_invariant_tags(), trust_types::TinvTagScan::None);
    }
    assert!(record.is_empty(), "the mint's walk recorded an installed fact");
}

// ---------------------------------------------------------------------------------------
// The post-call matrix
// ---------------------------------------------------------------------------------------

/// `fn g(self: &mut P, c: bool, z: u64) -> u8 { down(&mut *self); self.b[self.i] }` with
/// the shape knobs of the matrix. `&mut` entry facts are off, so the post-call fact is the
/// only source.
fn post_call(
    name: &str,
    identity: Option<CalleeIdentity>,
    two_preds: bool,
    write_between: bool,
) -> VerifiableFunction {
    // _2: c, _3: z, _4: the reborrow, _5: unit dest.
    let (locals, idx, len, ok) = index_locals(
        mutable(p_ty()),
        vec![
            (Ty::Bool, Some("c")),
            (u64_ty(), Some("z")),
            (mutable(p_ty()), None),
            (Ty::Unit, None),
        ],
    );
    let reborrow = assign(
        Place::local(4),
        Rvalue::Ref { mutable: true, place: proj(1, vec![Projection::Deref]) },
    );
    let down = call(
        "c::down",
        vec![Operand::Move(Place::local(4))],
        Place::local(5),
        1,
        identity,
        UnwindEdge::Continue,
    );
    let mut use_stmts = Vec::new();
    if write_between {
        use_stmts.push(assign(
            proj(1, vec![Projection::Deref, Projection::Field(1)]),
            Rvalue::Use(Operand::Copy(Place::local(3))),
        ));
    }
    use_stmts.extend(index_check(1, true, idx, len, ok));
    let blocks = if two_preds {
        // bb0: switch c -> bb2 | bb3; bb2: down -> bb1; bb3: goto bb1.
        vec![
            blk(
                0,
                vec![],
                Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            blk(1, use_stmts, bounds_assert(ok, 4)),
            blk(2, vec![reborrow], down),
            blk(3, vec![], Terminator::Goto(BlockId(1))),
            blk(4, vec![index_read(1, true, idx)], Terminator::Return),
        ]
    } else {
        vec![
            blk(0, vec![reborrow], down),
            blk(1, use_stmts, bounds_assert(ok, 2)),
            blk(2, vec![index_read(1, true, idx)], Terminator::Return),
        ]
    };
    func(name, locals, 3, blocks)
}

#[test]
fn post_call_matrix() {
    let not_inventory = CalleeIdentity { def_index: 42, ..DOWN };
    // (name, identity, two predecessors, write between, proves)
    let cases = [
        ("inventory", Some(DOWN), false, false, true),
        ("no_identity", None, false, false, false),
        ("outside", Some(not_inventory), false, false, false),
        ("two_preds", Some(DOWN), true, false, false),
        ("write_between", Some(DOWN), false, true, false),
    ];
    for (name, identity, two_preds, write, expect) in cases {
        let f = post_call(name, identity, two_preds, write);
        let set = use_set(&[&f.def_path]);
        let out = run(&f, Some(Arc::clone(&set)));
        let baseline = run(&f, None);
        if expect {
            assert!(out.all_proved && !baseline.all_proved, "{name}: {:?}", out.tags);
            assert_eq!(out.tags, vec![tag0(&set)], "{name}");
        } else {
            assert_eq!(out.verdicts, baseline.verdicts, "{name}: tags={:?}", out.tags);
        }
        if matches!(name, "no_identity" | "outside" | "two_preds") {
            assert!(out.tags.is_empty() && out.rows.is_empty(), "{name}: no post-call point");
        }
    }
}

/// A row in a block the call's target does not dominate gets no post-call fact: the read
/// sits in `bb3`, reached from `bb0` around the call.
#[test]
fn post_call_a_row_the_target_does_not_dominate_gets_no_fact() {
    // _2: c, _3: the reborrow, _4: unit dest.
    let (locals, idx, len, ok) = index_locals(
        mutable(p_ty()),
        vec![(Ty::Bool, Some("c")), (mutable(p_ty()), None), (Ty::Unit, None)],
    );
    let reborrow = assign(
        Place::local(3),
        Rvalue::Ref { mutable: true, place: proj(1, vec![Projection::Deref]) },
    );
    let f = func(
        "around",
        locals,
        2,
        vec![
            blk(
                0,
                vec![],
                Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            blk(
                1,
                vec![reborrow],
                call(
                    "c::down",
                    vec![Operand::Move(Place::local(3))],
                    Place::local(4),
                    2,
                    Some(DOWN),
                    UnwindEdge::Continue,
                ),
            ),
            blk(2, vec![], Terminator::Goto(BlockId(3))),
            blk(3, index_check(1, true, idx, len, ok), bounds_assert(ok, 4)),
            blk(4, vec![index_read(1, true, idx)], Terminator::Return),
        ],
    );
    // Control: the same call, the read in its target block, proves (the call DOES give a
    // fact here; only domination withholds it below).
    let set = use_set(&["c::around"]);
    let points = crate::type_invariant::obligations::post_call_assumption_points(
        &f,
        &crate::type_invariant::obligations::TinvInputs {
            ty: &p_tinv(),
            inventory: set.inventory(),
            models: &crate::type_invariant::unwind::SysrootExactModels,
            may_run_user_drop: &|_| true,
        },
    );
    assert_eq!(points.len(), 1, "the call is a post-call point");
    let out = run(&f, Some(Arc::clone(&set)));
    assert!(out.tags.is_empty() && out.rows.is_empty(), "{:?}", out.tags);
    assert_no_row_gained(&f, set, "around");
}

/// P5's field chain `feed(&mut self.s)`: the root is a field of another struct. The mint's
/// `post_call_assumption_points` admits it (design §5 P5), but the v1 USE SITE gives facts
/// only at a whole local or the pointee of one (decision TINV-24), so no fact.
#[test]
fn post_call_a_field_chain_root_is_not_eligible_at_the_use_site() {
    let q_ty = Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: "c::Q".into(),
        fields: vec![("s".to_string(), p_ty())].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let (locals, idx, len, ok) =
        index_locals(mutable(q_ty), vec![(mutable(p_ty()), None), (Ty::Unit, None)]);
    let s_of_self = vec![Projection::Deref, Projection::Field(0)];
    let field = |f: usize| {
        let mut p = s_of_self.clone();
        p.push(Projection::Field(f));
        p
    };
    let mut slice_read = field(0);
    slice_read.extend([Projection::Deref, Projection::Index(idx)]);
    let f = func(
        "feed_chain",
        locals,
        1,
        vec![
            blk(
                0,
                vec![assign(
                    Place::local(2),
                    Rvalue::Ref { mutable: true, place: proj(1, s_of_self.clone()) },
                )],
                call(
                    "c::down",
                    vec![Operand::Move(Place::local(2))],
                    Place::local(3),
                    1,
                    Some(DOWN),
                    UnwindEdge::Continue,
                ),
            ),
            blk(
                1,
                vec![
                    assign(Place::local(idx), Rvalue::Use(Operand::Copy(proj(1, field(1))))),
                    assign(
                        Place::local(len),
                        Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(proj(1, field(0)))),
                    ),
                    assign(
                        Place::local(ok),
                        Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(idx)),
                            Operand::Copy(Place::local(len)),
                        ),
                    ),
                ],
                bounds_assert(ok, 2),
            ),
            blk(
                2,
                vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(proj(1, slice_read))))],
                Terminator::Return,
            ),
        ],
    );
    let set = use_set(&["c::feed_chain"]);
    let points = crate::type_invariant::obligations::post_call_assumption_points(
        &f,
        &crate::type_invariant::obligations::TinvInputs {
            ty: &p_tinv(),
            inventory: set.inventory(),
            models: &crate::type_invariant::unwind::SysrootExactModels,
            may_run_user_drop: &|_| true,
        },
    );
    assert_eq!(points.len(), 1, "the mint's rule admits the field chain");
    let out = run(&f, Some(set));
    assert!(out.rows.is_empty() && out.tags.is_empty(), "a field-chain root got a fact");
}

// ---------------------------------------------------------------------------------------
// The record is scoped to ONE generation (review of 10.3, item 1)
// ---------------------------------------------------------------------------------------

/// A generation of the same body outside the recording scope (as the overflow-origin
/// replay was until T3 C05) and a probe of a clone (the inferred-return lane) neither get
/// facts nor pollute the record: the consumed generation's rows still carry exactly the
/// recorded tags, and the replayed rows carry none.
#[test]
fn a_replay_and_a_probe_outside_the_scope_neither_assume_nor_record() {
    let f = at("at", true);
    let set = use_set(&["c::at"]);
    let context = context_for(&f, Some(Arc::clone(&set)));
    // The replay BEFORE and AFTER the consumed generation, under the same context.
    let before = super::generate_vcs_with_context(&f, &context);
    let (consumed, record) = crate::type_invariant::with_tinv_assumed_rows_scope(&f, || {
        super::generate_vcs_with_context(&f, &context)
    });
    assert!(record.use_set.as_ref().is_some_and(|s| Arc::ptr_eq(s, &set)));
    let rows = record.rows;
    let after = super::generate_vcs_with_context(&f, &context);
    let probe = f.clone();
    let probed = super::generate_vcs_with_context(&probe, &context);
    assert_channels_agree(&consumed, &rows);
    assert_eq!(rows.len(), 1, "exactly the consumed generation's row: {rows:?}");
    assert!(index_rows(&consumed).iter().any(|vc| !formula_tags(vc).is_empty()));
    for replay in [&before, &after, &probed] {
        assert!(replay.iter().all(|vc| formula_tags(vc).is_empty()), "a replay assumed a fact");
        assert_eq!(format!("{replay:?}"), format!("{:?}", super::generate_vcs(&f)));
    }
    // Two consumed generations (a second walk inside one scope) still agree per key.
    let (twice, record) = crate::type_invariant::with_tinv_assumed_rows_scope(&f, || {
        let mut v = super::generate_vcs_with_context(&f, &context);
        v.extend(super::generate_vcs_with_context(&f, &context));
        v
    });
    let rows = record.rows;
    assert_channels_agree(&twice, &rows);
}

/// D5 through a real generation: a body with a tail call gets no fact even though it is
/// in `checked_bodies` and generation expands the tail call before the safety walk (the
/// scope decides on the UNEXPANDED body). Control: the same body without the tail call.
#[test]
fn a_tail_call_body_gets_no_fact_through_a_real_generation() {
    let f = at("at", true);
    let mut tail = f.clone();
    // bb1 ends in a tail call instead of `return`.
    tail.body.blocks[1].terminator = Terminator::TailCall {
        func: "c::k".into(),
        args: Vec::new(),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
    };
    let set = use_set(&["c::at"]);
    let (vcs, rows) = generate(&f, Some(Arc::clone(&set)));
    assert!(!rows.is_empty() && vcs.iter().any(|vc| !formula_tags(vc).is_empty()), "control");
    let (vcs, rows) = generate(&tail, Some(set));
    assert!(rows.is_empty(), "a tail-call body recorded a fact: {rows:?}");
    assert!(vcs.iter().all(|vc| formula_tags(vc).is_empty()), "a tail-call body assumed a fact");
}

// ---------------------------------------------------------------------------------------
// 10.3-LEN: the indirect reseat channels of a `&[T]` field (review of 10.3, item 3)
// ---------------------------------------------------------------------------------------

/// `fn f(mut self: P, o: &[u8]) -> u8 { <reseat self.b>; self.b[self.i] }` for the three
/// indirect channels: `&mut self.b` handed to an OPAQUE call, `&mut self.b` handed to a
/// call whose DERIVED write-set stores `(*arg)`, and `r = &mut self.b; *r = copy o`.
/// Each changes no verdict; the control without the reseat proves only under the set.
#[test]
fn len_an_indirect_reseat_of_the_slice_field_binds_nothing_at_the_use_site() {
    use crate::generate::callee_write_set::{
        CalleeWritePath, CalleeWriteSet, enter_test_callee_write_sets,
    };
    #[derive(Clone, Copy, Debug)]
    enum Reseat {
        Unchanged,
        Opaque,
        DerivedWriteSet,
        StoreThroughAlias,
    }
    let build = |name: &str, how: Reseat| {
        // _2: o, _3: &mut &[u8], _4: unit dest.
        let (locals, idx, len, ok) = index_locals(
            p_ty(),
            vec![(slice_ref(), Some("o")), (mutable(slice_ref()), Some("r")), (Ty::Unit, None)],
        );
        let field0 = proj(1, vec![Projection::Field(0)]);
        let borrow = assign(Place::local(3), Rvalue::Ref { mutable: true, place: field0 });
        let mut blocks = Vec::new();
        let check = index_check(1, false, idx, len, ok);
        match how {
            Reseat::Opaque | Reseat::DerivedWriteSet => {
                let callee = if matches!(how, Reseat::Opaque) { "c::opaque" } else { "c::put" };
                blocks.push(blk(
                    0,
                    vec![borrow],
                    call(
                        callee,
                        vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(2))],
                        Place::local(4),
                        1,
                        None,
                        UnwindEdge::Continue,
                    ),
                ));
                blocks.push(blk(1, check, bounds_assert(ok, 2)));
                blocks.push(blk(2, vec![index_read(1, false, idx)], Terminator::Return));
            }
            Reseat::Unchanged => {
                blocks.push(blk(0, check, bounds_assert(ok, 1)));
                blocks.push(blk(1, vec![index_read(1, false, idx)], Terminator::Return));
            }
            Reseat::StoreThroughAlias => {
                let mut bb0 = vec![
                    borrow,
                    assign(
                        proj(3, vec![Projection::Deref]),
                        Rvalue::Use(Operand::Copy(Place::local(2))),
                    ),
                ];
                bb0.extend(check);
                blocks.push(blk(0, bb0, bounds_assert(ok, 1)));
                blocks.push(blk(1, vec![index_read(1, false, idx)], Terminator::Return));
            }
        }
        func(name, locals, 2, blocks)
    };
    // `c::put(r: &mut &[u8], o: &[u8]) { *r = o }`: its write-set stores `(*arg0)`.
    let _ws = enter_test_callee_write_sets(
        [(
            "c::put".to_string(),
            CalleeWriteSet {
                paths: vec![CalleeWritePath { formal: 1, projections: vec![Projection::Deref] }],
            },
        )]
        .into_iter()
        .collect(),
    );
    // The pre-change control: the same body with no reseat proves only under the set.
    let control = build("unchanged", Reseat::Unchanged);
    assert!(run(&control, Some(use_set(&["c::unchanged"]))).all_proved, "control, with the set");
    assert!(!run(&control, None).all_proved, "control, without the set");
    for how in [Reseat::Opaque, Reseat::DerivedWriteSet, Reseat::StoreThroughAlias] {
        let name = format!("{how:?}").to_lowercase();
        let f = build(&name, how);
        let set = use_set(&[&f.def_path]);
        // The length name is re-versioned after the change (the oracle half).
        let sv = super::stmt_versions_for(&f);
        let (b, k) = match how {
            Reseat::StoreThroughAlias => (0, 2),
            _ => (1, 0),
        };
        assert_eq!(sv.version_token_at(&f, BlockId(0), 0, "self.0__slice_len"), None);
        assert!(
            sv.version_token_at(&f, BlockId(b), k, "self.0__slice_len").is_some(),
            "{how:?}: the slice length is not re-versioned after the reseat"
        );
        let out = assert_no_row_gained(&f, set, &name);
        assert!(!out.tags.is_empty(), "{how:?}: the entry fact is conjoined and binds nothing");
    }
}

/// Two DIFFERENT installed sets inside one recording scope are flagged, so the consumer
/// refuses every tagged row of that generation (it cannot decode against one set).
#[test]
fn two_sets_in_one_scope_are_flagged_as_conflicting() {
    let f = at("at", true);
    let (a, b) = (use_set(&["c::at"]), use_set(&["c::at"]));
    let (_, record) = crate::type_invariant::with_tinv_assumed_rows_scope(&f, || {
        super::generate_vcs_with_context(&f, &context_for(&f, Some(Arc::clone(&a))));
        super::generate_vcs_with_context(&f, &context_for(&f, Some(Arc::clone(&b))));
    });
    assert!(record.conflicting_sets);
    assert!(record.carries_premise());
}

// ---------------------------------------------------------------------------------------
// Step 10.6: destination roots
// ---------------------------------------------------------------------------------------

/// `fn mk(o: &[u8]) -> u8 { let p: P = new(o); p.b[p.i] }`: the call's DESTINATION, a whole
/// local of type exactly `P`, gets a post-call fact when `new` is in the inventory (the
/// callee owes R on `_0`), and the row proves. Controls, each with no fact: a callee outside
/// the inventory or with no identity; a destination of type `Option<P>`-like (another
/// type); a field-projection destination; a write between the call and the read.
#[test]
fn dest_a_whole_local_destination_of_an_inventory_call_gets_a_fact() {
    // _0: u8, _1: o, _2: p (dest), _3.._5: idx/len/ok.
    let build = |name: &str, identity: Option<CalleeIdentity>, dest_ty: Ty, write: bool| {
        let (locals, idx, len, ok) = {
            let mut locals: Locals = vec![(u8_ty(), None), (slice_ref(), Some("o"))];
            locals.push((dest_ty, Some("p")));
            let idx = locals.len();
            locals.extend([(u64_ty(), None), (u64_ty(), None), (Ty::Bool, None)]);
            (locals, idx, idx + 1, idx + 2)
        };
        let mut bb1 = Vec::new();
        if write {
            bb1.push(assign(
                proj(2, vec![Projection::Field(1)]),
                Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(7, 64))),
            ));
        }
        bb1.extend(index_check(2, false, idx, len, ok));
        func(
            name,
            locals,
            1,
            vec![
                blk(
                    0,
                    vec![],
                    call(
                        "c::new",
                        vec![Operand::Copy(Place::local(1))],
                        Place::local(2),
                        1,
                        identity,
                        UnwindEdge::Continue,
                    ),
                ),
                blk(1, bb1, bounds_assert(ok, 2)),
                blk(2, vec![index_read(2, false, idx)], Terminator::Return),
            ],
        )
    };
    let inp_points = |f: &VerifiableFunction, set: &TinvUseSet| {
        crate::type_invariant::obligations::post_call_assumption_points(
            f,
            &crate::type_invariant::obligations::TinvInputs {
                ty: &p_tinv(),
                inventory: set.inventory(),
                models: &crate::type_invariant::unwind::SysrootExactModels,
                may_run_user_drop: &|_| true,
            },
        )
    };
    let positive = build("mk", Some(DOWN), p_ty(), false);
    let set = use_set(&["c::mk"]);
    let points = inp_points(&positive, &set);
    assert_eq!(points.len(), 1, "{points:?}");
    assert_eq!(points[0].kind, crate::type_invariant::obligations::PostCallRoot::Dest);
    assert_eq!(points[0].root, Place::local(2));
    let out = run(&positive, Some(Arc::clone(&set)));
    let baseline = run(&positive, None);
    assert!(out.all_proved && !baseline.all_proved, "{:?}", out.tags);
    assert_eq!(out.tags, vec![tag0(&set)]);

    // Not in the inventory, or no identity: no point, no fact.
    let outside = CalleeIdentity { stable_crate_id: 1, def_index: 99, substs_digest: [0, 0] };
    for (name, identity) in [("mk_outside", Some(outside)), ("mk_none", None)] {
        let f = build(name, identity, p_ty(), false);
        let set = use_set(&[&format!("c::{name}")]);
        assert!(inp_points(&f, &set).is_empty(), "{name}");
        let out = assert_no_row_gained(&f, set, name);
        assert!(out.tags.is_empty() && out.rows.is_empty(), "{name}");
    }
    // A destination of another type (a wrapper around `P`): no point.
    let wrapper = Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: "c::Wrap".into(),
        fields: p_fields().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let f = build("mk_wrap", Some(DOWN), wrapper, false);
    let set = use_set(&["c::mk_wrap"]);
    assert!(inp_points(&f, &set).is_empty());
    // A write to the destination between the call and the read: the row stays failed.
    let f = build("mk_write", Some(DOWN), p_ty(), true);
    let set = use_set(&["c::mk_write"]);
    assert_eq!(inp_points(&f, &set).len(), 1, "the call is still a point");
    assert_no_row_gained(&f, set, "a write after the call");
}

/// A field-projection destination (`q.p = new(o)`) is never a destination root.
#[test]
fn dest_a_projected_destination_is_not_a_root() {
    let q_ty = Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: "c::Q".into(),
        fields: vec![("p".to_string(), p_ty())].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let f = func(
        "mk_field",
        vec![(Ty::Unit, None), (slice_ref(), Some("o")), (q_ty, Some("q"))],
        1,
        vec![
            blk(
                0,
                vec![],
                call(
                    "c::new",
                    vec![Operand::Copy(Place::local(1))],
                    proj(2, vec![Projection::Field(0)]),
                    1,
                    Some(DOWN),
                    UnwindEdge::Continue,
                ),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    );
    let set = use_set(&["c::mk_field"]);
    let points = crate::type_invariant::obligations::post_call_assumption_points(
        &f,
        &crate::type_invariant::obligations::TinvInputs {
            ty: &p_tinv(),
            inventory: set.inventory(),
            models: &crate::type_invariant::unwind::SysrootExactModels,
            may_run_user_drop: &|_| true,
        },
    );
    assert!(points.is_empty(), "{points:?}");
}

/// Step 10.6 flips `TINV_MUT_ENTRY_FACTS` on (decision TINV-31, after the rail-23 test
/// above passed its soundness half): with NO override, an `&mut P` parameter's pointee gets
/// the entry fact, and the `&mut self` index read proves. Control: the override off.
#[test]
fn mut_entry_facts_are_on_by_default_after_step_10_6() {
    assert!(super::type_invariant_facts::TINV_MUT_ENTRY_FACTS);
    let (locals, idx, len, ok) = index_locals(mutable(p_ty()), vec![]);
    let f = func(
        "at_mut",
        locals,
        1,
        vec![
            blk(0, index_check(1, true, idx, len, ok), bounds_assert(ok, 1)),
            blk(1, vec![index_read(1, true, idx)], Terminator::Return),
        ],
    );
    let set = use_set(&["c::at_mut"]);
    let on = run(&f, Some(Arc::clone(&set)));
    assert!(on.all_proved, "{:?}", on.tags);
    assert_eq!(on.tags, vec![tag0(&set)]);
    let _off = super::type_invariant_facts::override_mut_entry_facts(false);
    let off = run(&f, Some(set));
    assert!(!off.all_proved && off.tags.is_empty());
}

// ---------------------------------------------------------------------------------------
// TINV-31 review: the `&mut S` POINTEE variants of the 10.3-LEN use-site cases (the
// `TINV_MUT_ENTRY_FACTS` flip rests on them), and a destination root reseated after the
// call
// ---------------------------------------------------------------------------------------

/// `fn reseat(self: &mut P, o: &[u8]) -> u8 { self.b = o; self.b[self.i] }`: with the
/// `&mut` entry channel ON (the default since 10.6), the store re-versions
/// `self*.0__slice_len`, so the entry fact binds the OLD length and no index row is
/// gained. Control: without the store the row proves only under the set.
#[test]
fn len_mut_pointee_a_store_to_the_slice_field_reversions_its_length_at_the_use_site() {
    assert!(super::type_invariant_facts::TINV_MUT_ENTRY_FACTS);
    let build = |store: bool| {
        let (locals, idx, len, ok) = index_locals(mutable(p_ty()), vec![(slice_ref(), Some("o"))]);
        let mut bb0 = Vec::new();
        if store {
            bb0.push(assign(
                proj(1, vec![Projection::Deref, Projection::Field(0)]),
                Rvalue::Use(Operand::Copy(Place::local(2))),
            ));
        }
        bb0.extend(index_check(1, true, idx, len, ok));
        func(
            if store { "reseat_mut" } else { "keep_mut" },
            locals,
            2,
            vec![
                blk(0, bb0, bounds_assert(ok, 1)),
                blk(1, vec![index_read(1, true, idx)], Terminator::Return),
            ],
        )
    };
    let keep = run(&build(false), Some(use_set(&["c::keep_mut"])));
    assert!(keep.all_proved, "control: the `&mut` entry fact discharges the unchanged row");
    assert!(!run(&build(false), None).all_proved, "control: without the set it does not");
    let f = build(true);
    let sv = super::stmt_versions_for(&f);
    assert_eq!(sv.version_token_at(&f, BlockId(0), 0, "self*.0__slice_len"), None);
    assert!(
        sv.version_token_at(&f, BlockId(0), 1, "self*.0__slice_len").is_some(),
        "the pointee's slice length is not re-versioned after the store"
    );
    let out = assert_no_row_gained(&f, use_set(&["c::reseat_mut"]), "reseat_mut");
    assert!(!out.tags.is_empty(), "the `&mut` entry fact is conjoined and binds nothing");
}

/// The three INDIRECT reseat channels of the pointee's `&[u8]` field
/// (`fn f(self: &mut P, o: &[u8])`): `&mut (*self).b` handed to an OPAQUE call, to a call
/// whose DERIVED write-set stores `(*arg0)`, and `r = &mut (*self).b; *r = copy o`. Each
/// re-versions `self*.0__slice_len` and gains no row; the unchanged control proves only
/// under the set.
#[test]
fn len_mut_pointee_an_indirect_reseat_of_the_slice_field_binds_nothing_at_the_use_site() {
    use crate::generate::callee_write_set::{
        CalleeWritePath, CalleeWriteSet, enter_test_callee_write_sets,
    };
    #[derive(Clone, Copy, Debug)]
    enum Reseat {
        Unchanged,
        Opaque,
        DerivedWriteSet,
        StoreThroughAlias,
    }
    assert!(super::type_invariant_facts::TINV_MUT_ENTRY_FACTS);
    let build = |name: &str, how: Reseat| {
        // _2: o, _3: &mut &[u8], _4: unit dest.
        let (locals, idx, len, ok) = index_locals(
            mutable(p_ty()),
            vec![(slice_ref(), Some("o")), (mutable(slice_ref()), Some("r")), (Ty::Unit, None)],
        );
        let field0 = proj(1, vec![Projection::Deref, Projection::Field(0)]);
        let borrow = assign(Place::local(3), Rvalue::Ref { mutable: true, place: field0 });
        let mut blocks = Vec::new();
        let check = index_check(1, true, idx, len, ok);
        match how {
            Reseat::Opaque | Reseat::DerivedWriteSet => {
                let callee = if matches!(how, Reseat::Opaque) { "c::opaque" } else { "c::put" };
                blocks.push(blk(
                    0,
                    vec![borrow],
                    call(
                        callee,
                        vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(2))],
                        Place::local(4),
                        1,
                        None,
                        UnwindEdge::Continue,
                    ),
                ));
                blocks.push(blk(1, check, bounds_assert(ok, 2)));
                blocks.push(blk(2, vec![index_read(1, true, idx)], Terminator::Return));
            }
            Reseat::Unchanged => {
                blocks.push(blk(0, check, bounds_assert(ok, 1)));
                blocks.push(blk(1, vec![index_read(1, true, idx)], Terminator::Return));
            }
            Reseat::StoreThroughAlias => {
                let mut bb0 = vec![
                    borrow,
                    assign(
                        proj(3, vec![Projection::Deref]),
                        Rvalue::Use(Operand::Copy(Place::local(2))),
                    ),
                ];
                bb0.extend(check);
                blocks.push(blk(0, bb0, bounds_assert(ok, 1)));
                blocks.push(blk(1, vec![index_read(1, true, idx)], Terminator::Return));
            }
        }
        func(name, locals, 2, blocks)
    };
    let _ws = enter_test_callee_write_sets(
        [(
            "c::put".to_string(),
            CalleeWriteSet {
                paths: vec![CalleeWritePath { formal: 1, projections: vec![Projection::Deref] }],
            },
        )]
        .into_iter()
        .collect(),
    );
    let control = build("unchanged_mut", Reseat::Unchanged);
    assert!(
        run(&control, Some(use_set(&["c::unchanged_mut"]))).all_proved,
        "control, with the set"
    );
    assert!(!run(&control, None).all_proved, "control, without the set");
    for how in [Reseat::Opaque, Reseat::DerivedWriteSet, Reseat::StoreThroughAlias] {
        let name = format!("{how:?}_mut").to_lowercase();
        let f = build(&name, how);
        let set = use_set(&[&f.def_path]);
        let sv = super::stmt_versions_for(&f);
        let (b, k) = match how {
            Reseat::StoreThroughAlias => (0, 2),
            _ => (1, 0),
        };
        assert_eq!(sv.version_token_at(&f, BlockId(0), 0, "self*.0__slice_len"), None);
        assert!(
            sv.version_token_at(&f, BlockId(b), k, "self*.0__slice_len").is_some(),
            "{how:?}: the pointee's slice length is not re-versioned after the reseat"
        );
        // MEASURED: on the pointee the index row carries no tag at all here (a `&mut`
        // of the field reaches a call or a store, and no fact is given past it) — the
        // stronger, fail-closed outcome; either way no row is gained.
        assert_no_row_gained(&f, set, &name);
    }
}

/// `fn shrink(s: &mut S) { Vec::clear(&mut (*s).v); (*s).v[(*s).k] }` and the same with
/// `push`, on the `&mut S` POINTEE: the `&mut` call on the `Vec` field re-versions the
/// field's length name, and no index row is gained.
#[test]
fn len_mut_pointee_a_mut_call_on_the_vec_field_never_lets_the_entry_fact_discharge_the_index() {
    assert!(super::type_invariant_facts::TINV_MUT_ENTRY_FACTS);
    let vec_ty = Ty::Seq { elem: Box::new(u8_ty()), drop_auth: None };
    let s_fields = vec![("v".to_string(), vec_ty.clone()), ("k".to_string(), u64_ty())];
    let s_ty = Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: "c::S".into(),
        fields: s_fields.clone().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let t = TinvType {
        def_path: "c::S".into(),
        fields: s_fields,
        conjuncts: vec![CandidateConjunct {
            id: 0,
            formula: Formula::Lt(
                Box::new(field_var(FieldTerm::Value(1))),
                Box::new(field_var(FieldTerm::Len(0))),
            ),
        }],
    };
    let set_for = |body: &str| {
        let out = TinvOutcome::<()> {
            certificates: [(t.def_path.clone(), TypeInvariantCertificate::for_test(&t))]
                .into_iter()
                .collect(),
            inventory: [DOWN].into_iter().collect(),
            checked_bodies: [body.to_string()].into_iter().collect(),
            ..TinvOutcome::default()
        };
        Arc::new(TinvUseSet::from_outcome(&out, |_| true).expect("use set"))
    };
    let index = "<alloc::vec::Vec<u8> as core::ops::index::Index<usize>>::index";
    let root = Place { local: 1, projections: vec![Projection::Deref] };
    let build = |name: &str, callee: &str, extra: Vec<Operand>| {
        let vref = |m: bool| Ty::Ref { mutable: m, inner: Box::new(vec_ty.clone()) };
        let field0 = proj(1, vec![Projection::Deref, Projection::Field(0)]);
        let mut args = vec![Operand::Move(Place::local(2))];
        args.extend(extra);
        func(
            name,
            vec![
                (Ty::Unit, None),
                (mutable(s_ty.clone()), Some("self")),
                (vref(true), None),
                (Ty::Unit, None),
                (vref(false), None),
                (u64_ty(), None),
                (Ty::Ref { mutable: false, inner: Box::new(u8_ty()) }, None),
            ],
            1,
            vec![
                blk(
                    0,
                    vec![assign(
                        Place::local(2),
                        Rvalue::Ref { mutable: true, place: field0.clone() },
                    )],
                    call(callee, args, Place::local(3), 1, None, UnwindEdge::Continue),
                ),
                blk(
                    1,
                    vec![
                        assign(Place::local(4), Rvalue::Ref { mutable: false, place: field0 }),
                        assign(
                            Place::local(5),
                            Rvalue::Use(Operand::Copy(proj(
                                1,
                                vec![Projection::Deref, Projection::Field(1)],
                            ))),
                        ),
                    ],
                    call(
                        index,
                        vec![Operand::Move(Place::local(4)), Operand::Move(Place::local(5))],
                        Place::local(6),
                        2,
                        None,
                        UnwindEdge::Continue,
                    ),
                ),
                blk(2, vec![], Terminator::Return),
            ],
        )
    };
    let x = Operand::Constant(trust_types::ConstValue::Uint(7, 8));
    for (name, callee, extra) in [
        ("shrink_mut", "alloc::vec::Vec::<u8>::clear", vec![]),
        ("grow_mut", "alloc::vec::Vec::<u8>::push", vec![x]),
    ] {
        let f = build(name, callee, extra);
        // The length name the entry fact reads is re-versioned after the call.
        let sigma = crate::type_invariant::obligations::sigma_of_root(&f, &t, &root);
        let Some(Some(Formula::Var(len, _))) = sigma.len.first().cloned() else {
            panic!("{name}: no Len term for field 0: {sigma:?}")
        };
        let sv = super::stmt_versions_for(&f);
        assert_eq!(sv.version_token_at(&f, BlockId(0), 0, &len), None, "{name}: {len}");
        assert!(
            sv.version_token_at(&f, BlockId(1), 0, &len).is_some(),
            "{name}: `{len}` is not re-versioned after the `&mut` call"
        );
        // MEASURED: no tag reaches the `Vec` index row here (fail closed); no row gained.
        assert_no_row_gained(&f, set_for(&f.def_path), name);
    }
}

/// `fn mk(o: &[u8], q: &[u8]) -> u8 { let mut p: P = new(o); <reseat p.b to q>; p.b[p.i] }`
/// with `new` in the inventory: the DESTINATION root's post-call fact is sealed at the
/// call's target, and a reseat of `p.b` between the call and the read — directly
/// (`p.b = q`) or through an alias (`r = &mut p.b; *r = q`) — re-versions
/// `p.0__slice_len`, so no row is gained. Control: no reseat, the row proves under the set.
#[test]
fn dest_a_reseat_of_the_destinations_slice_field_after_the_call_binds_nothing() {
    #[derive(Clone, Copy, Debug)]
    enum Reseat {
        None,
        Direct,
        ThroughAlias,
    }
    // _0: u8, _1: o, _2: q, _3: p (dest), _4: r, _5.._7: idx/len/ok.
    let build = |name: &str, how: Reseat| {
        let locals: Locals = vec![
            (u8_ty(), None),
            (slice_ref(), Some("o")),
            (slice_ref(), Some("q")),
            (p_ty(), Some("p")),
            (mutable(slice_ref()), Some("r")),
            (u64_ty(), None),
            (u64_ty(), None),
            (Ty::Bool, None),
        ];
        let (idx, len, ok) = (5, 6, 7);
        let field0 = proj(3, vec![Projection::Field(0)]);
        let mut bb1 = match how {
            Reseat::None => vec![],
            Reseat::Direct => {
                vec![assign(field0, Rvalue::Use(Operand::Copy(Place::local(2))))]
            }
            Reseat::ThroughAlias => vec![
                assign(Place::local(4), Rvalue::Ref { mutable: true, place: field0 }),
                assign(
                    proj(4, vec![Projection::Deref]),
                    Rvalue::Use(Operand::Copy(Place::local(2))),
                ),
            ],
        };
        let read_at = bb1.len();
        bb1.extend(index_check(3, false, idx, len, ok));
        (
            func(
                name,
                locals,
                2,
                vec![
                    blk(
                        0,
                        vec![],
                        call(
                            "c::new",
                            vec![Operand::Copy(Place::local(1))],
                            Place::local(3),
                            1,
                            Some(DOWN),
                            UnwindEdge::Continue,
                        ),
                    ),
                    blk(1, bb1, bounds_assert(ok, 2)),
                    blk(2, vec![index_read(3, false, idx)], Terminator::Return),
                ],
            ),
            read_at,
        )
    };
    let (control, _) = build("mk_keep", Reseat::None);
    let with = run(&control, Some(use_set(&["c::mk_keep"])));
    assert!(with.all_proved && !run(&control, None).all_proved, "control: {:?}", with.tags);
    for how in [Reseat::Direct, Reseat::ThroughAlias] {
        let name = format!("mk_{how:?}").to_lowercase();
        let (f, read_at) = build(&name, how);
        let sv = super::stmt_versions_for(&f);
        assert_ne!(
            sv.version_token_at(&f, BlockId(1), read_at, "p.0__slice_len"),
            sv.version_token_at(&f, BlockId(1), 0, "p.0__slice_len"),
            "{how:?}: the destination's slice length is not re-versioned by the reseat"
        );
        let out = assert_no_row_gained(&f, use_set(&[&f.def_path]), &name);
        assert!(!out.tags.is_empty(), "{how:?}: the post-call fact is conjoined and binds nothing");
    }
}
