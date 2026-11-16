//! TINV 10.3-LEN (step-10 plan, landed FIRST, before any use-site fact): a type-invariant
//! ENTRY fact is conjoined over the BARE names `sigma_of_root` renders, and the version
//! oracle must re-version every such name the body changes. For a field's LENGTH term that
//! is not a place the body writes directly: a `Vec` field's length is the field's own
//! Int-sorted name (`guards::coll_len_var_place`), and a `&[T]` field's length is the
//! derived `{field}__slice_len`. If a `&mut` call on the field (`clear`, `push`) or a store
//! of a new slice to it left the length name bare, the entry fact `k < len(v)` would bind
//! the length AFTER the change and prove an out-of-bounds read.
//!
//! Each case checks, at the point after the change, that (a) the oracle versions the
//! length name, (b) the entry channel the use site will use
//! (`conjoin_preconditions_versioned_at_point_recorded`, the channel the TINV mint already
//! assumes through) leaves `entry ∧ ¬I` SATISFIABLE, i.e. the entry fact does not
//! discharge the post-change row; and, as the control, that before the change the same
//! row is UNSAT. Cases: a by-value `S` parameter (the root step 10.2 gives entry facts
//! for), and the `&mut S` pointee (the root the mint assumes at, behind G14).
use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition, VerificationResult,
};

use super::{conjoin_preconditions_versioned_at_point_recorded, version_rename_at};
use crate::type_invariant::obligations::sigma_of_root;
use crate::type_invariant::{CandidateConjunct, FieldTerm, TinvType, field_var, instantiate};

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn u8_ty() -> Ty {
    Ty::Int { width: 8, signed: false }
}

fn vec_ty() -> Ty {
    Ty::Seq { elem: Box::new(u8_ty()), drop_auth: None }
}

fn slice_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(u8_ty()) }) }
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

/// `c::S { v: Vec<u8>, k: u64 }` or `c::T { b: &[u8], k: u64 }`, with `I = k < len(f0)`.
fn tinv(name: &str, f0: Ty) -> (Ty, TinvType) {
    let fields = vec![("f0".to_string(), f0), ("k".to_string(), u64_ty())];
    let ty = adt(name, &[("f0", fields[0].1.clone()), ("k", u64_ty())]);
    let t = TinvType {
        def_path: name.into(),
        fields,
        conjuncts: vec![CandidateConjunct {
            id: 0,
            formula: Formula::Lt(
                Box::new(field_var(FieldTerm::Value(1))),
                Box::new(field_var(FieldTerm::Len(0))),
            ),
        }],
    };
    (ty, t)
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

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn call(callee: &str, args: Vec<Operand>, dest: Place, target: usize) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest,
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Continue,
        callee_identity: None,
        callee_key: None,
    }
}

fn blk(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

/// The root's field-0 place: `s.0` for a by-value root, `(*self).0` for a pointee.
fn f0(root: &Place) -> Place {
    let mut p = root.clone();
    p.projections.push(Projection::Field(0));
    p
}

/// `bb0: [_2 = &mut root.0]; callee(move _2, extra..) -> bb1; bb1: return`.
fn mut_call_body(
    name: &str,
    root_ty: Ty,
    root: &Place,
    callee: &str,
    extra: Vec<Operand>,
) -> VerifiableFunction {
    let mut args = vec![Operand::Move(Place::local(2))];
    args.extend(extra);
    func(
        name,
        vec![
            (Ty::Unit, None),
            (root_ty, Some(if root.projections.is_empty() { "s" } else { "self" })),
            (Ty::Ref { mutable: true, inner: Box::new(vec_ty()) }, None),
            (Ty::Unit, None),
        ],
        1,
        vec![
            blk(
                0,
                vec![assign(Place::local(2), Rvalue::Ref { mutable: true, place: f0(root) })],
                call(callee, args, Place::local(3), 1),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    )
}

/// `fn f(mut s: T, o: &[u8]) { s.b = o; }`: `bb0: [s.0 = copy _2]; goto bb1; bb1: return`.
fn slice_store_body(root_ty: Ty) -> VerifiableFunction {
    func(
        "reseat",
        vec![(Ty::Unit, None), (root_ty, Some("s")), (slice_ref(), Some("o"))],
        2,
        vec![
            blk(
                0,
                vec![assign(f0(&Place::local(1)), Rvalue::Use(Operand::Copy(Place::local(2))))],
                Terminator::Goto(BlockId(1)),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    )
}

fn solve(formula: &Formula) -> VerificationResult {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "tinv len".into() },
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

/// The entry instance `I(σ(root))`, its length name, and the formula the entry channel
/// builds at `(block, point)` for `entry ∧ ¬I`.
fn entry_row(
    func: &VerifiableFunction,
    t: &TinvType,
    root: &Place,
    block: usize,
    point: usize,
) -> (Formula, String, Formula) {
    let sigma = sigma_of_root(func, t, root);
    let instance = instantiate(&t.conjuncts[0], &sigma).expect("instantiable");
    let Some(Some(Formula::Var(len, _))) = sigma.len.first().cloned() else {
        panic!("no Len term for field 0: {sigma:?}")
    };
    let (formula, _) = conjoin_preconditions_versioned_at_point_recorded(
        func,
        BlockId(block),
        point,
        std::slice::from_ref(&instance),
        &Default::default(),
        Formula::Not(Box::new(instance.clone())),
    );
    (instance, len, formula)
}

/// The 10.3-LEN property for one body: the length name is bare at `(0, 0)` and re-versioned
/// at `after`; the entry row is UNSAT before the change and SAT after it.
fn assert_len_reversioned(
    func: &VerifiableFunction,
    t: &TinvType,
    root: &Place,
    after: (usize, usize),
) {
    let sv = super::stmt_versions_for(func);
    let (instance, len, before_row) = entry_row(func, t, root, 0, 0);
    assert_eq!(sv.version_token_at(func, BlockId(0), 0, &len), None, "{len} at entry");
    let token = sv.version_token_at(func, BlockId(after.0), after.1, &len);
    assert!(
        token.is_some(),
        "`{len}` is NOT re-versioned at bb{}[{}] of {}",
        after.0,
        after.1,
        func.name
    );
    assert_ne!(
        version_rename_at(&instance, &sv, func, BlockId(after.0), after.1),
        instance,
        "the instance reads entry names after the change"
    );
    let r = solve(&before_row);
    assert!(
        matches!(r, VerificationResult::Proved { .. }),
        "control, before the change: {r:?}\n{before_row:?}"
    );
    let (_, _, after_row) = entry_row(func, t, root, after.0, after.1);
    let r = solve(&after_row);
    assert!(
        matches!(r, VerificationResult::Failed { .. }),
        "the entry fact discharged the post-change row in {}: {r:?}\n{after_row:?}",
        func.name
    );
}

#[test]
fn a_vec_clear_on_a_by_value_root_reversions_the_length() {
    let (ty, t) = tinv("c::S", vec_ty());
    let root = Place::local(1);
    let f = mut_call_body("clear_val", ty, &root, "alloc::vec::Vec::<u8>::clear", vec![]);
    assert_len_reversioned(&f, &t, &root, (1, 0));
}

#[test]
fn a_vec_push_on_a_by_value_root_reversions_the_length() {
    let (ty, t) = tinv("c::S", vec_ty());
    let root = Place::local(1);
    let x = Operand::Constant(trust_types::ConstValue::Uint(7, 8));
    let f = mut_call_body("push_val", ty, &root, "alloc::vec::Vec::<u8>::push", vec![x]);
    assert_len_reversioned(&f, &t, &root, (1, 0));
}

#[test]
fn a_vec_clear_through_a_mut_pointee_reversions_the_length() {
    let (ty, t) = tinv("c::S", vec_ty());
    let root = Place { local: 1, projections: vec![Projection::Deref] };
    let f = mut_call_body(
        "clear_mut",
        Ty::Ref { mutable: true, inner: Box::new(ty) },
        &root,
        "alloc::vec::Vec::<u8>::clear",
        vec![],
    );
    assert_len_reversioned(&f, &t, &root, (1, 0));
}

#[test]
fn a_slice_store_on_a_by_value_root_reversions_the_slice_length() {
    let (ty, t) = tinv("c::T", slice_ref());
    let root = Place::local(1);
    let f = slice_store_body(ty);
    // Both the point right after the store and the next block.
    assert_len_reversioned(&f, &t, &root, (0, 1));
    assert_len_reversioned(&f, &t, &root, (1, 0));
}

/// Review of 10.3, item 3: the INDIRECT reseat channels of a `&[u8]` field's length.
/// `fn f(mut s: T, o: &[u8])` with `_3: &mut &[u8] = &mut s.0`, then either
/// (a) `c::opaque(move _3, copy o)` with no write-set (conservative havoc), or the same
/// call to `c::put`, whose DERIVED write-set stores `(*arg0)` (installed for the oracle);
/// or (b) `(*_3) = copy o` (a store through the alias). In each, the slice length is
/// re-versioned after the change, and the entry row is UNSAT before it and SAT after it.
#[test]
fn an_indirect_reseat_of_a_slice_field_reversions_its_length() {
    use crate::generate::callee_write_set::{
        CalleeWritePath, CalleeWriteSet, enter_test_callee_write_sets,
    };
    let (ty, t) = tinv("c::T", slice_ref());
    let root = Place::local(1);
    let locals = || {
        vec![
            (Ty::Unit, None),
            (ty.clone(), Some("s")),
            (slice_ref(), Some("o")),
            (Ty::Ref { mutable: true, inner: Box::new(slice_ref()) }, Some("r")),
            (Ty::Unit, None),
        ]
    };
    let borrow = || assign(Place::local(3), Rvalue::Ref { mutable: true, place: f0(&root) });
    let via_call = |name: &str, callee: &str| {
        func(
            name,
            locals(),
            2,
            vec![
                blk(
                    0,
                    vec![borrow()],
                    call(
                        callee,
                        vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(2))],
                        Place::local(4),
                        1,
                    ),
                ),
                blk(1, vec![], Terminator::Return),
            ],
        )
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
    assert_len_reversioned(&via_call("reseat_opaque", "c::opaque"), &t, &root, (1, 0));
    assert_len_reversioned(&via_call("reseat_put", "c::put"), &t, &root, (1, 0));
    let alias = func(
        "reseat_alias",
        locals(),
        2,
        vec![
            blk(
                0,
                vec![
                    borrow(),
                    assign(
                        Place { local: 3, projections: vec![Projection::Deref] },
                        Rvalue::Use(Operand::Copy(Place::local(2))),
                    ),
                ],
                Terminator::Goto(BlockId(1)),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    );
    assert_len_reversioned(&alias, &t, &root, (0, 2));
    assert_len_reversioned(&alias, &t, &root, (1, 0));
}

/// TINV-31 review: the `&mut T` POINTEE twin of the slice-store case, the root the `&mut`
/// entry channel (`TINV_MUT_ENTRY_FACTS`, on since 10.6) gives facts at:
/// `fn f(self: &mut T, o: &[u8]) { (*self).b = o; }`. `self*.0__slice_len` is
/// re-versioned after the store, and the entry row is UNSAT before it and SAT after it.
#[test]
fn a_slice_store_through_a_mut_pointee_reversions_the_slice_length() {
    let (ty, t) = tinv("c::T", slice_ref());
    let root = Place { local: 1, projections: vec![Projection::Deref] };
    let f = func(
        "reseat_mut",
        vec![
            (Ty::Unit, None),
            (Ty::Ref { mutable: true, inner: Box::new(ty) }, Some("self")),
            (slice_ref(), Some("o")),
        ],
        2,
        vec![
            blk(
                0,
                vec![assign(f0(&root), Rvalue::Use(Operand::Copy(Place::local(2))))],
                Terminator::Goto(BlockId(1)),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    );
    let sv = super::stmt_versions_for(&f);
    assert!(sv.version_token_at(&f, BlockId(0), 1, "self*.0__slice_len").is_some());
    assert_len_reversioned(&f, &t, &root, (0, 1));
    assert_len_reversioned(&f, &t, &root, (1, 0));
}

/// TINV-31 review: the INDIRECT reseat channels on the `&mut T` POINTEE —
/// `&mut (*self).b` to an opaque call, to `c::put` (derived write-set `(*arg0)`), and
/// `r = &mut (*self).b; *r = copy o`. Each re-versions `self*.0__slice_len`.
#[test]
fn an_indirect_reseat_of_a_slice_field_through_a_mut_pointee_reversions_its_length() {
    use crate::generate::callee_write_set::{
        CalleeWritePath, CalleeWriteSet, enter_test_callee_write_sets,
    };
    let (ty, t) = tinv("c::T", slice_ref());
    let root = Place { local: 1, projections: vec![Projection::Deref] };
    let locals = || {
        vec![
            (Ty::Unit, None),
            (Ty::Ref { mutable: true, inner: Box::new(ty.clone()) }, Some("self")),
            (slice_ref(), Some("o")),
            (Ty::Ref { mutable: true, inner: Box::new(slice_ref()) }, Some("r")),
            (Ty::Unit, None),
        ]
    };
    let borrow = || assign(Place::local(3), Rvalue::Ref { mutable: true, place: f0(&root) });
    let via_call = |name: &str, callee: &str| {
        func(
            name,
            locals(),
            2,
            vec![
                blk(
                    0,
                    vec![borrow()],
                    call(
                        callee,
                        vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(2))],
                        Place::local(4),
                        1,
                    ),
                ),
                blk(1, vec![], Terminator::Return),
            ],
        )
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
    for f in [via_call("reseat_opaque_mut", "c::opaque"), via_call("reseat_put_mut", "c::put")] {
        let sv = super::stmt_versions_for(&f);
        assert!(sv.version_token_at(&f, BlockId(1), 0, "self*.0__slice_len").is_some());
        assert_len_reversioned(&f, &t, &root, (1, 0));
    }
    let alias = func(
        "reseat_alias_mut",
        locals(),
        2,
        vec![
            blk(
                0,
                vec![
                    borrow(),
                    assign(
                        Place { local: 3, projections: vec![Projection::Deref] },
                        Rvalue::Use(Operand::Copy(Place::local(2))),
                    ),
                ],
                Terminator::Goto(BlockId(1)),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    );
    let sv = super::stmt_versions_for(&alias);
    assert!(sv.version_token_at(&alias, BlockId(0), 2, "self*.0__slice_len").is_some());
    assert_len_reversioned(&alias, &t, &root, (0, 2));
    assert_len_reversioned(&alias, &t, &root, (1, 0));
}
