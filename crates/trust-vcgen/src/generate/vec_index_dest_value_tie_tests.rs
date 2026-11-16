use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, SourceSpan, Statement, Terminator, Ty,
    UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::build_vec_index_dest_value_tie_facts;

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}
fn usize_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}
fn vec_u32() -> Ty {
    Ty::adt("std::vec::Vec<u32>", vec![])
}
fn shared_vec() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(vec_u32()) }
}
fn elem_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(u32_ty()) }
}
fn index_call(recv: usize, idx: usize, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: "<std::vec::Vec<u32> as core::ops::index::Index<usize>>::index".to_string(),
        args: vec![Operand::Copy(Place::local(recv)), Operand::Copy(Place::local(idx))],
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(
            "<std::vec::Vec<u32> as core::ops::index::Index<usize>>::index",
        ),
        is_foreign: false,
    }
}

/// `fn f(v: &Vec<u32>, i: usize)` with TWO `<Vec as Index>::index(v, _k)` calls
/// through distinct index temps — the guard-read / use-read pair of `v[i]`.
fn two_index_call_func() -> VerifiableFunction {
    VerifiableFunction {
        name: "two_calls".to_string(),
        def_path: "test::two_calls".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: shared_vec(), name: Some("v".into()) },
                LocalDecl { index: 2, ty: usize_ty(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: usize_ty(), name: None },
                LocalDecl { index: 4, ty: usize_ty(), name: None },
                LocalDecl { index: 5, ty: elem_ref(), name: None },
                LocalDecl { index: 6, ty: elem_ref(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: trust_types::Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: index_call(1, 3, 5, 1),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: trust_types::Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: index_call(1, 4, 6, 2),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Base case: two index calls on one shared-&Vec root emit exactly one
/// congruence fact `Or(idx_a != idx_b, (*dest_a) == (*dest_b))`.
#[test]
fn shared_vec_two_index_calls_emit_deref_congruence() {
    let func = two_index_call_func();
    let facts = build_vec_index_dest_value_tie_facts(&func);
    assert_eq!(facts.len(), 1, "expected one pair fact; got {facts:?}");
    match &facts[0] {
        Formula::Or(djs) => {
            assert_eq!(djs.len(), 2, "hypothesis + deref tie; got {djs:?}");
            assert!(matches!(&djs[0], Formula::Not(inner) if matches!(&**inner, Formula::Eq(..))));
            assert!(matches!(&djs[1], Formula::Eq(..)));
        }
        other => panic!("expected Or(..); got {other:?}"),
    }
}

/// N1 (fact level): a `&mut Vec` root must emit NOTHING (a resize/element write
/// between the two derefs would make the tie a false-PROVE vector).
#[test]
fn mut_vec_root_declines() {
    let mut func = two_index_call_func();
    func.body.locals[1].ty = Ty::Ref { mutable: true, inner: Box::new(vec_u32()) };
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// `index_mut` must decline even if the types looked right — its `&mut` result
/// can write the element between the derefs.
#[test]
fn index_mut_callee_declines() {
    let mut func = two_index_call_func();
    for b in &mut func.body.blocks {
        if let Terminator::Call { func: callee, .. } = &mut b.terminator {
            *callee =
                "<std::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::index_mut".to_string();
        }
    }
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// A user ADT named e.g. `MyVec` must NOT inherit the Vec element-immutability
/// tie (its `index` semantics are its own).
#[test]
fn user_adt_root_declines() {
    let mut func = two_index_call_func();
    func.body.locals[1].ty =
        Ty::Ref { mutable: false, inner: Box::new(Ty::adt("mycrate::MyVec", vec![])) };
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// A user ADT NAMED `Vec` must decline too: its `Index` impl is its own, and a safe
/// one that returns a different element on each call made the tie a false fact
/// (`tests/data/user_type_named_vec.rs`). The name test matched the path's tail until
/// 2026-09-30; it now matches std's own paths only (`is_owned_slice_container_name`).
#[test]
fn a_user_adt_named_vec_declines() {
    for name in ["mycrate::Vec", "user_type_named_vec::inner::Vec<usize>", "vec::Vec<u32>", "Vec"] {
        let mut func = two_index_call_func();
        func.body.locals[1].ty = Ty::Ref { mutable: false, inner: Box::new(Ty::adt(name, vec![])) };
        assert!(build_vec_index_dest_value_tie_facts(&func).is_empty(), "{name} must decline");
    }
    // std's own spellings still tie (the positive control for the same fixture).
    for name in ["std::vec::Vec<u32>", "alloc::vec::Vec<u32, alloc::alloc::Global>"] {
        let mut func = two_index_call_func();
        func.body.locals[1].ty = Ty::Ref { mutable: false, inner: Box::new(Ty::adt(name, vec![])) };
        assert!(!build_vec_index_dest_value_tie_facts(&func).is_empty(), "{name} must tie");
    }
}

/// A reseated root (`v = other;` between the calls) must emit NOTHING.
#[test]
fn reseated_root_declines() {
    let mut func = two_index_call_func();
    func.body.locals.push(LocalDecl { index: 7, ty: shared_vec(), name: None });
    func.body.blocks[1].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(1),
            rvalue: trust_types::Rvalue::Use(Operand::Copy(Place::local(7))),
            span: SourceSpan::default(),
        },
    );
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

// ── IDX-TIE-1 (2026-10-03): the tie is std's `Index<usize>` ONLY ─────────────
//
// The callee spellings below are the extractor's, measured on stage1-w10
// (`-Ztrust-dump=mir-only`): `<[u32] as core::ops::index::Index<usize>>::index`,
// `<[u32; 4] as core::ops::index::Index<usize>>::index` and
// `<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index`.

const STD_SLICE_INDEX: &str = "<[u32] as core::ops::index::Index<usize>>::index";

/// Replace the two index calls' callees, in block order.
fn with_callees(mut func: VerifiableFunction, first: &str, second: &str) -> VerifiableFunction {
    let mut names = [first, second].into_iter();
    for b in &mut func.body.blocks {
        if let Terminator::Call { func: callee, .. } = &mut b.terminator {
            *callee = names.next().expect("exactly two calls").to_string();
        }
    }
    func
}

/// The same body with a `&[u32]` root: the shape of the measured `idx2`/`idx3`
/// reproducers, and of an explicit `Index::index(v, i)` on a slice.
fn two_slice_index_calls(first: &str, second: &str) -> VerifiableFunction {
    let mut func = with_callees(two_index_call_func(), first, second);
    func.body.locals[1].ty =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(u32_ty()) }) };
    func
}

/// POSITIVE (the capability this keeps): std's slice `Index<usize>` pair ties.
#[test]
fn std_slice_index_pair_keeps_its_tie() {
    let func = two_slice_index_calls(STD_SLICE_INDEX, STD_SLICE_INDEX);
    assert_eq!(build_vec_index_dest_value_tie_facts(&func).len(), 1);
}

/// POSITIVE: the measured `alloc::vec::Vec` spelling on a std `Vec` root ties.
#[test]
fn std_vec_index_pair_in_the_extracted_spelling_keeps_its_tie() {
    let vec_index = "<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index";
    let func = with_callees(two_index_call_func(), vec_index, vec_index);
    assert_eq!(build_vec_index_dest_value_tie_facts(&func).len(), 1);
}

/// idx2: two user traits, each with a method named `index`, on `[u32]`. Nothing
/// ties their results; the measured build removed an overflow check on the tie.
#[test]
fn user_trait_methods_named_index_get_no_tie() {
    let func = two_slice_index_calls("<[u32] as idx2::Lo>::index", "<[u32] as idx2::Hi>::index");
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
    // One user trait called twice is no better: its body decides the result.
    let func =
        two_slice_index_calls("<[u32] as idx::Weird>::index", "<[u32] as idx::Weird>::index");
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// idx3: user `impl Index<A> for [u32]` and `impl Index<B> for [u32]` with local
/// key types. The trait IS core's, so a `core::ops::` substring anchor admits
/// them; the trait argument must be exactly `usize`. The extractor names these
/// calls by the resolved LOCAL impl (measured on stage1-w10:
/// `body::<impl core::ops::index::Index<body::A> for [u32]>::index`); the
/// trait-qualified spelling is declined too.
#[test]
fn user_index_impls_with_local_keys_get_no_tie() {
    let func = two_slice_index_calls(
        "idx3::<impl core::ops::index::Index<idx3::A> for [u32]>::index",
        "idx3::<impl core::ops::index::Index<idx3::B> for [u32]>::index",
    );
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
    let func = two_slice_index_calls(
        "<[u32] as core::ops::index::Index<idx3::A>>::index",
        "<[u32] as core::ops::index::Index<idx3::B>>::index",
    );
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// A key that merely ENDS in `usize` inside its own generics (`K<usize>`) is a
/// user type; the deque helper's `ends_with("<usize")` test would admit it.
#[test]
fn a_key_wrapping_usize_gets_no_tie() {
    let k = "<[u32] as core::ops::index::Index<idx::K<usize>>>::index";
    let func = two_slice_index_calls(k, k);
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// A std read paired with a user read: the group holds one std call, no pair.
#[test]
fn a_mixed_std_and_user_pair_gets_no_tie() {
    let func = two_slice_index_calls(STD_SLICE_INDEX, "<[u32] as idx2::Hi>::index");
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
    let func = two_slice_index_calls("<[u32] as idx2::Lo>::index", STD_SLICE_INDEX);
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// A user type NAMED `Vec` reaches std's `Vec` index through its own `Deref`,
/// which need not return the same `Vec` twice. The callee is std's, so the ROOT
/// must be std's `Vec` by exact path, not by last segment.
#[test]
fn a_user_type_named_vec_root_gets_no_tie() {
    let vec_index = "<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index";
    let mut func = with_callees(two_index_call_func(), vec_index, vec_index);
    func.body.locals[1].ty =
        Ty::Ref { mutable: false, inner: Box::new(Ty::adt("idx4b::Vec", vec![])) };
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// The predicate itself, over the spellings that must and must not name std's
/// scalar `Index<usize>`.
#[test]
fn std_scalar_index_predicate_accepts_exactly_std_impls() {
    use super::unwrap_panic::is_std_scalar_index_call as std_index;
    for yes in [
        STD_SLICE_INDEX,
        "<[u32; 4] as core::ops::index::Index<usize>>::index",
        "<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index",
        "<alloc::vec::Vec<alloc::vec::Vec<u32>> as core::ops::index::Index<usize>>::index",
        "<std::vec::Vec<u32> as core::ops::index::Index<usize>>::index",
        "<alloc::vec::Vec<T> as core::ops::Index<usize>>::index",
        "<[fn(u32) -> <u32 as core::ops::bit::Not>::Output {<u32 as core::ops::bit::Not>::not}] as core::ops::index::Index<usize>>::index",
    ] {
        assert!(std_index(yes), "must accept {yes}");
    }
    for no in [
        // user traits / user impls / user keys
        "<[u32] as idx2::Lo>::index",
        "<[u32] as core::ops::index::Index<idx3::A>>::index",
        "idx3::<impl core::ops::index::Index<idx3::A> for [u32]>::index",
        "<[u32] as core::ops::index::Index<idx::K<usize>>>::index",
        "<[u32] as core::ops::index::Index<idx::usize>>::index",
        // a user self type, a non-Vec std container, a lookalike path
        "<mycrate::Vec<u32> as core::ops::index::Index<usize>>::index",
        "<alloc::vec::VecLike<u32> as core::ops::index::Index<usize>>::index",
        "<alloc::collections::vec_deque::VecDeque<u32> as core::ops::index::Index<usize>>::index",
        // range indexing returns a sub-slice, not an element
        "<[u32] as core::ops::index::Index<core::ops::range::RangeFrom<usize>>>::index",
        // index_mut, a suffix after the method, an unqualified trait call
        "<[u32] as core::ops::index::IndexMut<usize>>::index_mut",
        "<[u32] as core::ops::index::Index<usize>>::index::<u8>",
        "core::ops::index::Index::index",
        "std::ops::Index::index",
        // a callee whose defining crate the producer stamped as an impersonator
        "__trust_crate@00000000000000aa::<[u32] as core::ops::index::Index<usize>>::index",
        // a free function named index
        "idx::index",
    ] {
        assert!(!std_index(no), "must decline {no}");
    }
}


// VEC-INDEX-TIE-HEAP-1: the Vec header's shared borrow does not protect its buffer.
mod heap_epochs {
    use super::*;
    use trust_types::{AssertMessage, BinOp, ConstValue, Projection, Rvalue, VcKind,
        VerificationCondition, VerificationResult};

    fn assign(local: usize, rvalue: Rvalue) -> Statement {
        Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
    }
    fn read(local: usize) -> Operand {
        Operand::Copy(Place { local, projections: vec![Projection::Deref] })
    }
    fn opaque_call(target: usize) -> Terminator {
        Terminator::Call {
            unwind: UnwindEdge::Unreachable, func: "test::mutate_saved_buffer".into(),
            args: vec![], dest: Place::local(10), target: Some(BlockId(target)),
            span: SourceSpan::default(), atomic: None, is_unsafe_sig: false,
            callee_identity: None, callee_key: None, is_foreign: false,
        }
    }
    /// The negative is `let a=v[i]; mutate_saved_buffer(); assert!(a==v[i]);`.
    /// The positive acquires both references first and then reads both without a call.
    fn pair(across_call: bool) -> VerifiableFunction {
        let mut f = two_index_call_func();
        f.body.locals.extend([
            LocalDecl { index: 7, ty: u32_ty(), name: Some("before".into()) },
            LocalDecl { index: 8, ty: u32_ty(), name: Some("after".into()) },
            LocalDecl { index: 9, ty: Ty::Bool, name: Some("same".into()) },
            LocalDecl { index: 10, ty: Ty::Unit, name: None },
        ]);
        let first_read = assign(7, Rvalue::Use(read(5)));
        let second_read = assign(8, Rvalue::Use(read(6)));
        let compare = assign(9, Rvalue::BinaryOp(BinOp::Eq,
            Operand::Copy(Place::local(7)), Operand::Copy(Place::local(8))));
        let assertion = Terminator::Assert {
            cond: Operand::Copy(Place::local(9)), expected: true,
            msg: AssertMessage::Custom("vector heap epoch equality".into()), target: BlockId(4),
            span: SourceSpan::default(), unwind: UnwindEdge::Unreachable,
        };
        if across_call {
            f.body.blocks[1].stmts = vec![first_read];
            f.body.blocks[1].terminator = opaque_call(2);
            f.body.blocks[2] = BasicBlock {
                id: BlockId(2), stmts: vec![assign(4,
                    Rvalue::Use(Operand::Copy(Place::local(2))))],
                terminator: index_call(1, 4, 6, 3),
            };
            f.body.blocks.push(BasicBlock { id: BlockId(3),
                stmts: vec![second_read, compare], terminator: assertion });
        } else {
            f.body.blocks[1].terminator = index_call(1, 4, 6, 3);
            f.body.blocks[2].terminator = Terminator::Unreachable;
            f.body.blocks.push(BasicBlock { id: BlockId(3),
                stmts: vec![first_read, second_read, compare], terminator: assertion });
        }
        f.body.blocks.push(BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return });
        f
    }
    fn equality_row(f: &VerifiableFunction) -> VerificationCondition {
        let rows: Vec<_> = crate::generate_vcs(f).into_iter().filter(|row|
            matches!(&row.kind, VcKind::Assertion { message }
                if message.contains("vector heap epoch equality"))).collect();
        assert_eq!(rows.len(), 1, "exact original assertion must remain: {rows:?}");
        rows.into_iter().next().unwrap()
    }
    fn solve(row: &VerificationCondition) -> VerificationResult {
        trust_router::Router::with_backends(vec![
            Box::new(trust_router::interval_backend::IntervalBackend),
            Box::new(crate::test_router::test_ay_backend()),
            Box::new(trust_router::ty_backend::TyBackend),
            Box::new(trust_router::constant_folder::ConstantFolderBackend),
        ]).verify_all(std::slice::from_ref(row)).into_iter().next().unwrap().1
    }
    #[test]
    fn saved_buffer_call_cannot_prove_equal_element_snapshots() {
        let f = pair(true);
        let row = equality_row(&f);
        assert!(!matches!(solve(&row), VerificationResult::Proved { .. }),
            "a nullary safe call can write a stashed buffer pointer: {row:?}");
    }
    #[test]
    fn same_epoch_element_reads_still_prove_equal() {
        let f = pair(false);
        let row = equality_row(&f);
        assert!(matches!(solve(&row), VerificationResult::Proved { .. }),
            "two current reads at the same element without an intervening effect: {row:?}");
    }
    #[test]
    fn indexed_pointees_are_effect_dependencies_not_vec_headers() {
        let f = pair(true);
        let defs = super::super::path_defs::terminator_def_names(&f, &f.body.blocks[1]);
        for local in [5, 6] {
            let expected = crate::place_to_var_name(&f,
                &Place { local, projections: vec![Projection::Deref] });
            assert!(defs.contains(&expected), "missing heap-content dependency {expected}: {defs:?}");
        }
        assert!(!defs.contains(&"v".to_string()), "buffer effects must not invent a Vec-header write: {defs:?}");
    }
    #[test]
    fn a_reassigned_index_cannot_select_a_global_element_tie() {
        let mut f = two_index_call_func();
        f.body.blocks[2].stmts.push(assign(3, Rvalue::Use(Operand::Constant(ConstValue::Uint(99, 64)))));
        assert!(build_vec_index_dest_value_tie_facts(&f).is_empty(),
            "a current index value is not the historical element-selection value");
    }
    #[test]
    fn a_call_on_only_one_join_predecessor_cannot_freeze_the_buffer() {
        let mut f = pair(true);
        f.body.blocks[1].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(2)), targets: vec![(0, BlockId(5))],
            otherwise: BlockId(2), exhaustive_enum_unreachable: false, span: SourceSpan::default(),
        };
        f.body.blocks.push(BasicBlock { id: BlockId(5), stmts: vec![], terminator: opaque_call(2) });
        let row = equality_row(&f);
        assert!(!matches!(solve(&row), VerificationResult::Proved { .. }),
            "one predecessor can change the contents before the join: {row:?}");
    }
    #[test]
    fn a_repeated_call_site_does_not_reuse_an_earlier_heap_epoch() {
        let mut f = pair(true);
        f.body.locals.push(LocalDecl { index: 11, ty: usize_ty(), name: Some("remaining".into()) });
        f.body.blocks[1].stmts.push(assign(11, Rvalue::Use(Operand::Copy(Place::local(2)))));
        f.body.blocks[1].terminator = opaque_call(5);
        f.body.blocks.push(BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(11)), targets: vec![(0, BlockId(2))],
            otherwise: BlockId(6), exhaustive_enum_unreachable: false, span: SourceSpan::default(),
        } });
        f.body.blocks.push(BasicBlock { id: BlockId(6), stmts: vec![assign(11,
            Rvalue::BinaryOp(BinOp::Sub, Operand::Copy(Place::local(11)),
                Operand::Constant(ConstValue::Uint(1, 64))))], terminator: opaque_call(5) });
        let row = equality_row(&f);
        assert!(!matches!(solve(&row), VerificationResult::Proved { .. }),
            "a repeated static call ID is not a dynamic heap epoch: {row:?}");
    }
    #[test]
    fn copies_of_index_references_keep_the_heap_dependency() {
        let mut f = pair(true);
        f.body.locals.push(LocalDecl { index: 11, ty: elem_ref(), name: Some("saved_ref".into()) });
        f.body.blocks[1].stmts.insert(0, assign(11,
            Rvalue::Use(Operand::Copy(Place::local(5)))));
        let expected = crate::place_to_var_name(&f,
            &Place { local: 11, projections: vec![Projection::Deref] });
        let defs = super::super::path_defs::terminator_def_names(&f, &f.body.blocks[1]);
        assert!(defs.contains(&expected), "copying a reference does not freeze its heap: {defs:?}");
        assert!(!defs.contains(&"v".to_string()));
    }
    #[test]
    fn drops_and_opaque_effects_also_invalidate_indexed_contents() {
        for term in [Terminator::Drop { place: Place::local(10), target: BlockId(2),
                span: SourceSpan::default(), unwind: UnwindEdge::Unreachable },
                Terminator::Opaque { targets: vec![BlockId(2)], kind: "unseen code".into(), span: SourceSpan::default() }] {
            let mut f = pair(true);
            f.body.blocks[1].terminator = term;
            let defs = super::super::path_defs::terminator_def_names(&f, &f.body.blocks[1]);
            let expected = crate::place_to_var_name(&f,
                &Place { local: 5, projections: vec![Projection::Deref] });
            assert!(defs.contains(&expected), "an effect must invalidate backing contents: {defs:?}");
        }
    }
    #[test]
    fn opaque_pointer_stores_use_the_same_indexed_content_dependency() {
        let mut f = pair(true);
        f.body.locals.push(LocalDecl { index: 11,
            ty: Ty::RawPtr { mutable: true, pointee: Box::new(u32_ty()) }, name: Some("raw".into()) });
        // Give the raw pointer an actual typed call definition before its store.
        // The call remains unmodeled; this test inspects alias dependencies only,
        // and grants no safety/provenance permission to the returned pointer.
        f.body.blocks[0].terminator = index_call(1, 3, 5, 5);
        let mut get_pointer = opaque_call(1);
        if let Terminator::Call { func, dest, .. } = &mut get_pointer {
            *func = "test::saved_buffer_pointer".into();
            *dest = Place::local(11);
        }
        f.body.blocks.push(BasicBlock { id: BlockId(5), stmts: vec![], terminator: get_pointer });
        f.body.blocks[1].stmts.push(Statement::Assign {
            place: Place { local: 11, projections: vec![Projection::Deref] },
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(99, 32))), span: SourceSpan::default(),
        });
        let expected = crate::place_to_var_name(&f,
            &Place { local: 5, projections: vec![Projection::Deref] });
        assert!(super::super::path_defs::function_havoc_names(&f).contains(&expected),
            "pointer-store aliases must use the same backing-content dependency");
    }
    #[test]
    fn cross_epoch_equality_never_obtains_a_clean_certificate() {
        let row = equality_row(&pair(true));
        assert!(trust_certify::certify_vc(&row).is_none(),
            "the real unproved source obligation must not receive a Clean certificate: {row:?}");
    }

    #[test]
    fn a_once_per_loop_copy_does_not_make_a_variant_selection_constant() {
        let mut f = two_index_call_func();
        f.body.locals.push(LocalDecl { index: 7, ty: usize_ty(), name: Some("counter".into()) });
        f.body.blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![assign(7,
                Rvalue::Use(Operand::Copy(Place::local(2))))], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock { id: BlockId(1), stmts: vec![assign(3,
                Rvalue::Use(Operand::Copy(Place::local(7))))], terminator: index_call(1, 3, 5, 2) },
            BasicBlock { id: BlockId(2), stmts: vec![assign(7,
                Rvalue::BinaryOp(BinOp::Sub, Operand::Copy(Place::local(7)),
                    Operand::Constant(ConstValue::Uint(1, 64)))), assign(4,
                Rvalue::Use(Operand::Copy(Place::local(7))))], terminator: index_call(1, 4, 6, 3) },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
        ];
        assert!(crate::local_defs::is_single_static_assignment(&f, 3));
        assert!(crate::local_defs::is_single_static_assignment(&f, 4));
        assert!(build_vec_index_dest_value_tie_facts(&f).is_empty(),
            "one static copy per iteration is not a constant selection value");
    }

}
