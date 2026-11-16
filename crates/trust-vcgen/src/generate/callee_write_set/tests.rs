// Unit tests for the MIR-derived callee write-set lane.
//
// Two obligations these tests exist to hold:
//   * the DERIVATION is total and fail-closed — every construct outside the
//     modeled fragment must yield `None`, never an empty (= "writes nothing")
//     write-set;
//   * the CALL-SITE refinement narrows only the argument roots and only to
//     paths the callee provably writes, and it must still KILL the field when
//     the callee does write it (the negative direction).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::*;
use crate::generate::terminator_def_names;

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

/// `struct Storage { flag: bool, other: u32 }` nested in `struct G { storage: Storage }`.
///
/// Both stamped `AdtKind::Struct`, as the extractor stamps every rustc struct. Since
/// UNION-SIBLING-WRITE-2 (2026-10-12) the refined call list carries the union cover of
/// each write path it spells, and an UNSTAMPED ADT is read as a possible union
/// (`path_defs::field_base_may_overlap_siblings`, fail-closed): the unstamped fixture
/// this was before would put `self*` on the list beside `self*.0.1`.
fn g_ty() -> Ty {
    let stamp = |mut ty: Ty| {
        if let Ty::Adt { adt_kind, .. } = &mut ty {
            *adt_kind = Some(trust_types::AdtKind::Struct);
        }
        ty
    };
    stamp(Ty::adt(
        "p::G",
        vec![(
            "storage".into(),
            stamp(Ty::adt(
                "p::Storage",
                vec![("flag".into(), Ty::Bool), ("other".into(), u32_ty())],
            )),
        )],
    ))
}

fn mut_g_ref() -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(g_ty()) }
}

fn field_place(local: usize, f0: usize, f1: usize) -> Place {
    Place {
        local,
        projections: vec![Projection::Deref, Projection::Field(f0), Projection::Field(f1)],
    }
}

/// `fn helper(&mut self)` whose single statement writes `(*self).storage.<field>`.
fn helper_writing_field(field: usize) -> VerifiableFunction {
    VerifiableFunction {
        name: "helper".into(),
        def_path: "p::G::helper".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: mut_g_ref(), name: Some("self".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: field_place(1, 0, field),
                    rvalue: Rvalue::Use(Operand::Constant(if field == 0 {
                        ConstValue::Bool(true)
                    } else {
                        ConstValue::Uint(1, 32)
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
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

/// `fn caller(&mut self)` that stores `(*self).storage.flag` then calls `p::G::helper`.
fn caller_calling(callee: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "caller".into(),
        def_path: "p::G::caller".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: mut_g_ref(), name: Some("self".into()) },
                LocalDecl { index: 2, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: field_place(1, 0, 0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(false))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Continue,
                        func: callee.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
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

fn map_with(callee: &str, ws: CalleeWriteSet) -> FxHashMap<String, CalleeWriteSet> {
    let mut m = FxHashMap::default();
    m.insert(callee.to_string(), ws);
    m
}

// ======================================================================
// Derivation
// ======================================================================

#[test]
fn derives_the_single_field_a_helper_writes() {
    let ws = derive_callee_write_set(&helper_writing_field(1))
        .expect("a plain field store off `&mut self` is inside the fragment");
    assert_eq!(
        ws.paths,
        vec![CalleeWritePath {
            formal: 1,
            projections: vec![Projection::Deref, Projection::Field(0), Projection::Field(1)],
        }],
        "the write-set must name exactly the field the callee stores"
    );
}

#[test]
fn a_local_temp_write_is_caller_invisible() {
    let mut f = helper_writing_field(1);
    f.body.locals.push(LocalDecl { index: 2, ty: u32_ty(), name: None });
    f.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 32))),
            span: SourceSpan::default(),
        },
    );
    let ws = derive_callee_write_set(&f).expect("a scalar temp store stays inside the fragment");
    assert_eq!(ws.paths.len(), 1, "only the formal-rooted write is caller-visible: {ws:?}");
}

#[test]
fn drop_terminator_fails_closed() {
    let mut f = helper_writing_field(1);
    f.body.blocks[0].terminator = Terminator::Drop {
        place: Place::local(1),
        target: BlockId(0),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Continue,
    };
    assert!(
        derive_callee_write_set(&f).is_none(),
        "drop glue runs arbitrary user code with &mut access — never narrow past it"
    );
}

#[test]
fn mutable_borrow_inside_the_callee_fails_closed() {
    let mut f = helper_writing_field(1);
    f.body.locals.push(LocalDecl {
        index: 2,
        ty: Ty::Ref { mutable: true, inner: Box::new(u32_ty()) },
        name: None,
    });
    f.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Ref { mutable: true, place: field_place(1, 0, 1) },
        span: SourceSpan::default(),
    });
    assert!(
        derive_callee_write_set(&f).is_none(),
        "a &mut alias into a formal can be written through out of sight of the place scan"
    );
}

#[test]
fn address_of_inside_the_callee_fails_closed() {
    let mut f = helper_writing_field(1);
    f.body.locals.push(LocalDecl {
        index: 2,
        ty: Ty::RawPtr { mutable: true, pointee: Box::new(u32_ty()) },
        name: None,
    });
    f.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::AddressOf(true, field_place(1, 0, 1)),
        span: SourceSpan::default(),
    });
    assert!(derive_callee_write_set(&f).is_none(), "raw-address laundering must fail closed");
}

#[test]
fn deref_store_through_a_local_fails_closed() {
    let mut f = helper_writing_field(1);
    f.body.locals.push(LocalDecl {
        index: 2,
        ty: Ty::Ref { mutable: true, inner: Box::new(u32_ty()) },
        name: None,
    });
    // `*p = 1` where `p` is a non-formal local: the pointee is unresolved here.
    f.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place { local: 2, projections: vec![Projection::Deref] },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 32))),
        span: SourceSpan::default(),
    }];
    assert!(
        derive_callee_write_set(&f).is_none(),
        "a store through an unresolved local pointer may reach caller memory"
    );
}

#[test]
fn nested_call_with_a_pointer_argument_fails_closed() {
    let mut f = helper_writing_field(1);
    f.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    f.body.blocks[0].terminator = Terminator::Call {
        unwind: UnwindEdge::Continue,
        func: "p::opaque".into(),
        // Passing the `&mut self` on: the nested callee can write anything.
        args: vec![Operand::Copy(Place::local(1))],
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key("p::opaque"),
        is_foreign: false,
    };
    assert!(
        derive_callee_write_set(&f).is_none(),
        "a nested call handed a pointer can reach caller memory transitively"
    );
}

#[test]
fn nested_call_with_only_scalar_arguments_is_admitted() {
    let mut f = helper_writing_field(1);
    f.body.locals.push(LocalDecl { index: 2, ty: u32_ty(), name: None });
    f.body.locals.push(LocalDecl { index: 3, ty: u32_ty(), name: None });
    f.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    f.body.blocks[0].terminator = Terminator::Call {
        unwind: UnwindEdge::Continue,
        func: "core::num::<impl u32>::wrapping_add".into(),
        args: vec![Operand::Move(Place::local(3)), Operand::Constant(ConstValue::Uint(1, 32))],
        dest: Place::local(2),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key("core::num::<impl u32>::wrapping_add"),
        is_foreign: false,
    };
    let ws = derive_callee_write_set(&f)
        .expect("a nested call over pure scalars cannot reach caller memory");
    assert_eq!(ws.paths.len(), 1, "the scalar dest is a caller-invisible temp: {ws:?}");
}

#[test]
fn write_through_a_pointer_nested_in_the_receiver_fails_closed() {
    // `(*self).storage.p` is a `&mut u32`; the callee stores `*((*self).storage.p)`.
    let inner = Ty::adt(
        "p::Storage",
        vec![
            ("flag".into(), Ty::Bool),
            ("p".into(), Ty::Ref { mutable: true, inner: Box::new(u32_ty()) }),
        ],
    );
    let g = Ty::adt("p::G", vec![("storage".into(), inner)]);
    let mut f = helper_writing_field(1);
    f.body.locals[1].ty = Ty::Ref { mutable: true, inner: Box::new(g) };
    f.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place {
            local: 1,
            projections: vec![
                Projection::Deref,
                Projection::Field(0),
                Projection::Field(1),
                Projection::Deref,
            ],
        },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(9, 32))),
        span: SourceSpan::default(),
    }];
    assert!(
        derive_callee_write_set(&f).is_none(),
        "the pointee of a nested &mut is an unnameable caller local — fail closed"
    );
}

/// `p::G { storage: Storage, k: <stored> }`: `G` with one more field, which holds
/// `stored` — a pointer the function never retagged when it sits behind a `&`.
fn g_with_stored(stored: Ty) -> Ty {
    let Ty::Adt { fields, .. } = g_ty() else { unreachable!() };
    let mut fields = fields.to_vec();
    fields.push(("k".into(), stored));
    Ty::adt("p::G", fields)
}

/// The stored pointers the receiver's pointee may hold BEHIND A SHARED REFERENCE that
/// are still a second hop out of the receiver's tree: a `&mut`, a raw pointer and a
/// `Box` (rendered with its fields), each behind a `&`. A copy of any of them — or a
/// raw child, derived before the call — writes the target with defined behaviour.
/// `ty_contains_mut_pointer`, which both refusals asked until 2026-09-30, does not
/// recurse through `&` and sees none of them.
fn stored_behind_shared() -> Vec<(&'static str, Ty)> {
    let shared = |t: Ty| Ty::Ref { mutable: false, inner: Box::new(t) };
    let boxed = Ty::adt(
        "alloc::boxed::Box<u32>",
        vec![(
            "0".into(),
            Ty::adt(
                "core::ptr::unique::Unique<u32>",
                vec![(
                    "pointer".into(),
                    Ty::adt(
                        "core::ptr::non_null::NonNull<u32>",
                        vec![(
                            "pointer".into(),
                            Ty::RawPtr { mutable: false, pointee: Box::new(u32_ty()) },
                        )],
                    ),
                )],
            ),
        )],
    );
    vec![
        ("& &mut u32", shared(Ty::Ref { mutable: true, inner: Box::new(u32_ty()) })),
        ("& *mut u32", shared(Ty::RawPtr { mutable: true, pointee: Box::new(u32_ty()) })),
        ("& Box<u32>", shared(boxed)),
    ]
}

/// The first refusal (`classify_write_place`, a write through a `&mut` formal) asks
/// the unretagged-pointer question of the formal's pointee, so a helper that writes
/// `(*self).storage.other` beside a `&mut`/raw pointer/`Box` stored behind a `&`
/// derives NO write-set. A frozen `&u32` there is not a second hop, and the same
/// helper still derives its one path. With `ty_contains_mut_pointer` put back here
/// the three refusals become write-sets (the r8c finish's mutant `MCWS`, which no
/// test killed before these two).
#[test]
fn a_pointer_stored_behind_a_shared_ref_in_the_formal_fails_closed() {
    let with_k = |stored: Ty| {
        let mut f = helper_writing_field(1);
        f.body.locals[1].ty = Ty::Ref { mutable: true, inner: Box::new(g_with_stored(stored)) };
        f
    };
    for (what, stored) in stored_behind_shared() {
        assert!(
            derive_callee_write_set(&with_k(stored)).is_none(),
            "a `{what}` in the receiver's pointee is a second hop: fail closed"
        );
    }
    let frozen = Ty::Ref { mutable: false, inner: Box::new(u32_ty()) };
    let ws = derive_callee_write_set(&with_k(frozen)).expect("a frozen `&u32` is no second hop");
    assert_eq!(ws.paths.len(), 1, "the one field the helper writes: {ws:?}");
}

/// The second refusal (`refine_call_havoc_delta`'s replaceable root) asks the same
/// question of the ACTUAL's pointee. A helper whose body writes nothing through
/// `self` derives an EMPTY write-set, so a replaceable root's base name would be
/// dropped with nothing put back — and with it the havoc of every place under
/// `self`, the target of the stored pointer included. The caller's own whole-local
/// `self` must stay on the list for each stored pointer; for a frozen `&u32` the root
/// IS replaced, which is what shows the refusal, not an inert lane, decides.
///
/// No real-MIR body reaches this end to end today: reading the target of a pointer
/// stored behind a `&` in `*self` takes two deref temporaries, and the second one's
/// pointee is never renamed to a place under `self`, so no fact about the target
/// crosses the call with or without the refusal
/// (tests/data/callee_write_set_unretagged.rs, `stored_mut_behind_shared`; the raw
/// and `Box` forms are refused earlier by `caller_admits_name_based_places`, because
/// their deref temporaries are raw pointers).
#[test]
fn a_pointer_stored_behind_a_shared_ref_in_the_pointee_is_not_a_replaceable_root() {
    let mut helper = helper_writing_field(1);
    helper.body.blocks[0].stmts.clear();
    let ws = derive_callee_write_set(&helper).expect("a helper that writes nothing");
    assert!(ws.paths.is_empty(), "the helper writes nothing: {ws:?}");
    let _scope = enter_test_callee_write_sets(map_with("p::G::helper", ws));

    let caller_with = |stored: Ty| {
        let mut caller = caller_calling("p::G::helper");
        caller.body.locals[1].ty =
            Ty::Ref { mutable: true, inner: Box::new(g_with_stored(stored)) };
        caller
    };
    for (what, stored) in stored_behind_shared() {
        let caller = caller_with(stored);
        let names = terminator_def_names(&caller, &caller.body.blocks[0]);
        assert!(
            names.iter().any(|n| n == "self"),
            "a `{what}` in the receiver's pointee keeps the whole-receiver havoc: {names:?}"
        );
    }
    // The control asks for the whole-receiver base name only. Since CALL-HAVOC-ESCAPE-2
    // (2026-10-06) every call also havocs `self*` here by a separate rule
    // (`path_defs::stored_ref_pointee_names`: `self` is handed to the call, so it is
    // not a pinned parameter and its pointee is memory behind an unretagged
    // reference), so "nothing under `self` dies" is no longer the refinement's
    // signature; the dropped base name `self` is.
    let caller = caller_with(Ty::Ref { mutable: false, inner: Box::new(u32_ty()) });
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(
        !names.iter().any(|n| n == "self"),
        "with only a frozen `&u32` beside it, the receiver's base name is replaced by what \
         the helper writes (nothing): {names:?}"
    );
}

// ======================================================================
// Call-site refinement — BOTH directions
// ======================================================================

/// POSITIVE: a helper that writes only `storage.other` leaves `self*.0.0` alive
/// across the call, so the flag store made before the call still reaches the
/// exit block.
#[test]
fn refined_call_keeps_the_untouched_sibling_field_alive() {
    let caller = caller_calling("p::G::helper");
    let ws = derive_callee_write_set(&helper_writing_field(1)).expect("in-fragment helper");
    let _scope = enter_test_callee_write_sets(map_with("p::G::helper", ws));

    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(
        names.iter().any(|n| n == "self*.0.1"),
        "the field the helper DOES write must be havoced: {names:?}"
    );
    assert!(
        !names.iter().any(|n| crate::generate::place_names_overlap(n, "self*.0.0")),
        "the field the helper does NOT write must survive the call: {names:?}"
    );
}

/// NEGATIVE — the direction that makes this lane worth anything: a helper that
/// DOES write the flagged field havocs it, exactly as the conservative lane did.
#[test]
fn refined_call_still_kills_a_field_the_callee_writes() {
    let caller = caller_calling("p::G::helper");
    let ws = derive_callee_write_set(&helper_writing_field(0)).expect("in-fragment helper");
    let _scope = enter_test_callee_write_sets(map_with("p::G::helper", ws));

    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(
        names.iter().any(|n| crate::generate::place_names_overlap(n, "self*.0.0")),
        "a helper that writes the flag MUST still havoc it: {names:?}"
    );
}

/// No installed write-set (an absent scope, a callee with no extracted body, or
/// a callee outside the fragment) keeps the conservative whole-receiver havoc.
#[test]
fn absent_write_set_keeps_the_conservative_havoc() {
    let caller = caller_calling("p::G::opaque");
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(
        names.iter().any(|n| n == "self"),
        "with no summary the whole receiver must still be havoced: {names:?}"
    );
}

/// A write-set for a DIFFERENT callee name must not be applied.
#[test]
fn write_set_is_keyed_by_callee_name() {
    let caller = caller_calling("p::G::other");
    let ws = derive_callee_write_set(&helper_writing_field(1)).expect("in-fragment helper");
    let _scope = enter_test_callee_write_sets(map_with("p::G::helper", ws));

    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(
        names.iter().any(|n| n == "self"),
        "a summary for another callee must not narrow this call: {names:?}"
    );
}

/// The lookup itself (PERF-COMPILER-VCGEN-521's `installed_write_set_map_for`, the
/// callee-keyed predicate the forgeable-key census classifies outside the
/// unsafe-contract mint, VCGEN-NINE-REDS-20261110). It answers only from the
/// INNERMOST scope and only for a name that scope's map holds: no scope, an
/// empty inner scope shadowing a populated outer one, and a name the map lacks
/// are each `None` — the conservative havoc — never a write-set of some other
/// callee.
#[test]
fn the_write_set_lookup_answers_only_the_innermost_scope_for_its_own_name() {
    assert!(installed_write_set_map_for("p::G::helper").is_none(), "no scope is active");
    let ws = derive_callee_write_set(&helper_writing_field(1)).expect("in-fragment helper");
    let _outer = enter_test_callee_write_sets(map_with("p::G::helper", ws.clone()));
    let map = installed_write_set_map_for("p::G::helper").expect("the name the map holds");
    assert_eq!(map.get("p::G::helper"), Some(&ws));
    assert!(installed_write_set_map_for("p::G::other").is_none(), "a name the map lacks");
    assert!(installed_write_set_map_for("p::G::helpe").is_none(), "a prefix is another name");
    {
        let _inner = enter_test_callee_write_sets(FxHashMap::default());
        assert!(
            installed_write_set_map_for("p::G::helper").is_none(),
            "an empty inner scope must not fall through to the outer map"
        );
    }
    assert!(installed_write_set_map_for("p::G::helper").is_some(), "the outer scope is back");
}

/// A caller carrying a RAW pointer local admits aliasing Rust's `&mut`
/// uniqueness rule does not cover, so the name-based refinement must refuse.
#[test]
fn caller_with_a_raw_pointer_local_refuses_the_refinement() {
    let mut caller = caller_calling("p::G::helper");
    caller.body.locals.push(LocalDecl {
        index: 3,
        ty: Ty::RawPtr { mutable: true, pointee: Box::new(u32_ty()) },
        name: None,
    });
    let ws = derive_callee_write_set(&helper_writing_field(1)).expect("in-fragment helper");
    let _scope = enter_test_callee_write_sets(map_with("p::G::helper", ws));

    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(
        names.iter().any(|n| n == "self"),
        "raw-pointer aliasing in the caller must keep the conservative havoc: {names:?}"
    );
}

/// An INDEX projection past the deref fails closed: element spellings have
/// aliasing rules this lane has not established.
#[test]
fn index_projection_in_a_write_path_fails_closed() {
    let mut f = helper_writing_field(1);
    f.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place {
            local: 1,
            projections: vec![Projection::Deref, Projection::Field(0), Projection::Index(2)],
        },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 32))),
        span: SourceSpan::default(),
    }];
    assert!(derive_callee_write_set(&f).is_none(), "index projections must fail closed");
}

/// An atomic RMW riding a `Call` terminator writes its own place; refuse.
#[test]
fn atomic_call_fails_closed() {
    let mut f = helper_writing_field(1);
    let Terminator::Return = f.body.blocks[0].terminator else { unreachable!() };
    f.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    f.body.blocks[0].terminator = Terminator::Call {
        unwind: UnwindEdge::Continue,
        func: "core::sync::atomic::AtomicU32::fetch_add".into(),
        args: vec![Operand::Constant(ConstValue::Uint(1, 32))],
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: Some(trust_types::AtomicOperation {
            place: field_place(1, 0, 0),
            dest: None,
            op_kind: trust_types::AtomicOpKind::FetchAdd,
            ordering: trust_types::AtomicOrdering::SeqCst,
            failure_ordering: None,
            span: SourceSpan::default(),
        }),
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(
            "core::sync::atomic::AtomicU32::fetch_add",
        ),
        is_foreign: false,
    };
    assert!(
        derive_callee_write_set(&f).is_none(),
        "an atomic's own written place is a second write channel — fail closed"
    );
}

/// A PROJECTED actual (`f(&mut s.0)` reached through a `&mut`-typed field) is
/// not a replaceable root: dropping the base name `s` would also un-havoc its
/// sibling `s.1`.
#[test]
fn projected_actual_is_not_a_replaceable_root() {
    let mut caller = caller_calling("p::G::helper");
    // Retype local 1 as a tuple of two `&mut G` and pass `Copy(_1.0)`.
    caller.body.locals[1].ty = Ty::Tuple(vec![mut_g_ref(), mut_g_ref()]);
    if let Terminator::Call { args, .. } = &mut caller.body.blocks[0].terminator {
        *args = vec![Operand::Copy(Place { local: 1, projections: vec![Projection::Field(0)] })];
    }
    let ws = derive_callee_write_set(&helper_writing_field(1)).expect("in-fragment helper");
    let _scope = enter_test_callee_write_sets(map_with("p::G::helper", ws));

    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(
        names.iter().any(|n| n == "self"),
        "a projected actual must keep the conservative base havoc: {names:?}"
    );
}

/// A BY-VALUE (non-`&mut`) actual is not a replaceable root either: the callee
/// cannot write the caller's local through it, but the local may still be in the
/// conservative set for reasons unrelated to this call.
#[test]
fn by_value_actual_is_not_a_replaceable_root() {
    let mut caller = caller_calling("p::G::helper");
    caller.body.locals.push(LocalDecl { index: 3, ty: u32_ty(), name: Some("n".into()) });
    // `&mut n` somewhere in the body puts `n` in the conservative alias set.
    caller.body.locals.push(LocalDecl {
        index: 4,
        ty: Ty::Ref { mutable: true, inner: Box::new(u32_ty()) },
        name: None,
    });
    caller.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(3) },
        span: SourceSpan::default(),
    });
    if let Terminator::Call { args, .. } = &mut caller.body.blocks[0].terminator {
        *args = vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(3))];
    }
    let ws = derive_callee_write_set(&helper_writing_field(1)).expect("in-fragment helper");
    let _scope = enter_test_callee_write_sets(map_with("p::G::helper", ws));

    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(
        names.iter().any(|n| n == "n"),
        "a by-value scalar actual must not drop that local's conservative havoc: {names:?}"
    );
    assert!(
        names.iter().any(|n| n == "self*.0.1"),
        "the &mut receiver root is still refined: {names:?}"
    );
}

/// A write path through a formal that is NOT a replaceable root refuses the
/// whole refinement (the havoc would otherwise be dropped without replacement).
#[test]
fn write_path_outside_a_replaceable_root_refuses() {
    let caller = caller_calling("p::G::helper");
    // A write-set claiming formal 2 — a formal this one-argument call does not
    // supply as a replaceable root.
    let ws = CalleeWriteSet {
        paths: vec![CalleeWritePath {
            formal: 2,
            projections: vec![Projection::Deref, Projection::Field(0)],
        }],
    };
    let _scope = enter_test_callee_write_sets(map_with("p::G::helper", ws));

    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(
        names.iter().any(|n| n == "self"),
        "an unmappable write path must keep the conservative havoc: {names:?}"
    );
}

/// The call DESTINATION is never excused by a write-set.
#[test]
fn destination_is_always_havoced() {
    let caller = caller_calling("p::G::helper");
    let ws = derive_callee_write_set(&helper_writing_field(1)).expect("in-fragment helper");
    let _scope = enter_test_callee_write_sets(map_with("p::G::helper", ws));

    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    let dest = crate::place_to_var_name(&caller, &Place::local(2));
    assert!(names.contains(&dest), "the call dest must always be killed: {names:?}");
}

/// A refined write path carries its `__slice_len` twin: a path that holds a fat
/// pointer (`*s = t` of an `s: &mut &[u8]`) moves its length with it, and no
/// overlap reaches the derived name from the path (`_` is not a projection
/// separator). Without the twin, `if i <= s.len() { sset(s, t); &s[..i] }` was
/// PROVED and panicked (audit of `3b4293d06cb`, 2026-09-29;
/// `tests/ui/trust/callee_reseat_kills_the_length_refused.rs`).
#[test]
fn refined_write_path_carries_its_slice_len_twin() {
    let caller = caller_calling("p::G::helper");
    let ws = derive_callee_write_set(&helper_writing_field(1)).expect("in-fragment helper");
    let _scope = enter_test_callee_write_sets(map_with("p::G::helper", ws));

    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(names.iter().any(|n| n == "self*.0.1"), "the refined path: {names:?}");
    assert!(
        names.iter().any(|n| n == "self*.0.1__slice_len"),
        "the refined path's length twin: {names:?}"
    );
}
// ======================================================================
// Frozen leaves under a shared-reference argument (TRUST-10, 2026-09-24)
// ======================================================================
//
// `refine_shared_reborrow_havoc`: a call handed `&*self` from a `&mut self`
// method cannot change a scalar field of `*self` outside every `UnsafeCell` —
// the argument is protected for the call, so such a write is undefined
// behaviour. Everything else under `*self` must stay havoced, and every other
// conservative name must stay in the list.

/// A struct as the extractor lowers one from a rustc `AdtDef` (`adt_kind`).
fn extracted_struct(name: &str, fields: Vec<(String, Ty)>) -> Ty {
    let mut ty = Ty::adt(name, fields);
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(trust_types::AdtKind::Struct);
    }
    ty
}

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

/// `struct S { n: u64, v: [u32; 4] }` — one frozen scalar, one opaque sibling.
fn s_ty() -> Ty {
    extracted_struct(
        "p::S",
        vec![("n".into(), u64_ty()), ("v".into(), Ty::Array { elem: Box::new(u32_ty()), len: 4 })],
    )
}

fn call_to(callee: &str, args: Vec<Operand>, dest: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Continue,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(callee),
        is_foreign: false,
    }
}

/// `fn remove(&mut self)` whose bb0 is `_2 = &(*_1)<proj>; p::S::check(move _2)`.
/// `pointee` is `*self`'s type and `reborrow` the place `_2` borrows.
fn caller_with_shared_reborrow(pointee: Ty, reborrow: Place, borrow_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "remove".into(),
        def_path: "p::S::remove".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(pointee) },
                    name: Some("self".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(borrow_ty) },
                    name: None,
                },
                LocalDecl { index: 3, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: reborrow },
                        span: SourceSpan::default(),
                    }],
                    terminator: call_to("p::S::check", vec![Operand::Move(Place::local(2))], 3),
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
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

fn whole_self_reborrow(pointee: Ty) -> VerifiableFunction {
    caller_with_shared_reborrow(
        pointee.clone(),
        Place { local: 1, projections: vec![Projection::Deref] },
        pointee,
    )
}

fn self_field(path: &[usize]) -> String {
    let mut s = String::from("self*");
    for i in path {
        s.push_str(&format!(".{i}"));
    }
    s
}

/// Does any havoc name in `names` rebind the read `read`?
fn rebinds(names: &[String], read: &str) -> bool {
    names.iter().any(|n| crate::generate::write_rebinds(n, read))
}

#[test]
fn a_shared_reborrow_call_keeps_the_frozen_scalar_field() {
    let caller = whole_self_reborrow(s_ty());
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(!names.iter().any(|n| n == "self"), "the base name must be refined away: {names:?}");
    assert!(
        !rebinds(&names, &self_field(&[0])),
        "`self.n` is a frozen scalar under the protected `&*self`: {names:?}"
    );
    // Everything else under `*self` is still havoced — the opaque sibling, its
    // elements, its derived length, and the whole pointee.
    for read in ["self*.1", "self*.1[_5]", "self*.1__slice_len", "self*"] {
        assert!(rebinds(&names, read), "`{read}` must stay havoced: {names:?}");
    }
    let dest = crate::place_to_var_name(&caller, &Place::local(3));
    assert!(names.contains(&dest), "the call dest is always killed: {names:?}");
}

#[test]
fn a_mutable_reborrow_argument_keeps_the_full_havoc() {
    let mut caller = whole_self_reborrow(s_ty());
    caller.body.locals[2].ty = Ty::Ref { mutable: true, inner: Box::new(s_ty()) };
    caller.body.blocks[0].stmts[0] = Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Ref {
            mutable: true,
            place: Place { local: 1, projections: vec![Projection::Deref] },
        },
        span: SourceSpan::default(),
    };
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(rebinds(&names, &self_field(&[0])), "`&mut *self` can write `n`: {names:?}");
}

#[test]
fn a_scalar_inside_an_unsafe_cell_stays_havoced() {
    // `struct T { c: Cell<u64>, m: u64 }`, with `Cell { value: UnsafeCell { value } }`.
    let unsafe_cell = extracted_struct("core::cell::UnsafeCell", vec![("value".into(), u64_ty())]);
    let cell = extracted_struct("core::cell::Cell", vec![("value".into(), unsafe_cell)]);
    let t = extracted_struct("p::T", vec![("c".into(), cell), ("m".into(), u64_ty())]);
    let caller = whole_self_reborrow(t);
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(
        rebinds(&names, &self_field(&[0, 0, 0])),
        "a `Cell`'s value is mutable through `&self`: {names:?}"
    );
    assert!(!rebinds(&names, &self_field(&[1])), "the plain `m` beside it is frozen: {names:?}");
}

#[test]
fn a_field_reborrow_exempts_only_what_it_covers() {
    // `struct O { a: u64, b: I }`, `struct I { c: u64, d: [u32; 4] }`, reborrow `&(*self).b`.
    let inner = extracted_struct(
        "p::I",
        vec![("c".into(), u64_ty()), ("d".into(), Ty::Array { elem: Box::new(u32_ty()), len: 4 })],
    );
    let outer = extracted_struct("p::O", vec![("a".into(), u64_ty()), ("b".into(), inner.clone())]);
    let caller = caller_with_shared_reborrow(
        outer,
        Place { local: 1, projections: vec![Projection::Deref, Projection::Field(1)] },
        inner,
    );
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(!rebinds(&names, &self_field(&[1, 0])), "`b.c` is covered and frozen: {names:?}");
    assert!(rebinds(&names, &self_field(&[1, 1])), "`b.d` is opaque: {names:?}");
    assert!(
        rebinds(&names, &self_field(&[0])),
        "`a` is outside the reborrow — the argument's protection does not reach it: {names:?}"
    );
}

#[test]
fn no_frozen_leaf_keeps_the_conservative_list_unchanged() {
    // `&(*self).v` covers only the array: nothing to exempt, so the list must be
    // the conservative one, byte for byte.
    let caller = caller_with_shared_reborrow(
        s_ty(),
        Place { local: 1, projections: vec![Projection::Deref, Projection::Field(1)] },
        Ty::Array { elem: Box::new(u32_ty()), len: 4 },
    );
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(names.iter().any(|n| n == "self"), "{names:?}");
}

#[test]
fn a_reborrow_with_a_second_value_keeps_the_full_havoc() {
    let mut caller = whole_self_reborrow(s_ty());
    let again = caller.body.blocks[0].stmts[0].clone();
    caller.body.blocks[0].stmts.push(again);
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(names.iter().any(|n| n == "self"), "{names:?}");
}

#[test]
fn an_escaped_receiver_keeps_the_full_havoc() {
    // `_4 = &mut _1`: a callee holding it could reseat `self` itself.
    let mut caller = whole_self_reborrow(s_ty());
    caller.body.locals.push(LocalDecl {
        index: 4,
        ty: Ty::Ref { mutable: true, inner: Box::new(caller.body.locals[1].ty.clone()) },
        name: None,
    });
    caller.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
        span: SourceSpan::default(),
    });
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(rebinds(&names, &self_field(&[0])), "{names:?}");
}

#[test]
fn a_mutable_borrow_through_the_receiver_keeps_the_refinement() {
    // `_4 = &mut (*_1).1` — a `&mut self` method borrowing a field, as bit-vec's
    // `remove` does with `self.storage` after its `&self` call. The borrow hands out
    // the POINTEE; it cannot reseat `self`, so `self.n` stays frozen at the call. It
    // is the one shape a whole-local `Escape` refusal wrongly blocked.
    let mut caller = whole_self_reborrow(s_ty());
    caller.body.locals.push(LocalDecl {
        index: 4,
        ty: Ty::Ref {
            mutable: true,
            inner: Box::new(Ty::Array { elem: Box::new(u32_ty()), len: 4 }),
        },
        name: None,
    });
    caller.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Ref {
            mutable: true,
            place: Place { local: 1, projections: vec![Projection::Deref, Projection::Field(1)] },
        },
        span: SourceSpan::default(),
    });
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(!rebinds(&names, &self_field(&[0])), "`self.n` is still frozen: {names:?}");
    assert!(rebinds(&names, &self_field(&[1])), "`self.v` is still havoced: {names:?}");
}

#[test]
fn foreign_unsafe_or_atomic_calls_keep_the_full_havoc() {
    for which in 0..3 {
        let mut caller = whole_self_reborrow(s_ty());
        let Terminator::Call { is_foreign, is_unsafe_sig, atomic, .. } =
            &mut caller.body.blocks[0].terminator
        else {
            unreachable!()
        };
        match which {
            0 => *is_foreign = true,
            1 => *is_unsafe_sig = true,
            _ => {
                *atomic = Some(trust_types::AtomicOperation {
                    place: Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Field(0)],
                    },
                    dest: None,
                    op_kind: trust_types::AtomicOpKind::Store,
                    ordering: trust_types::AtomicOrdering::SeqCst,
                    failure_ordering: None,
                    span: SourceSpan::default(),
                })
            }
        }
        let names = terminator_def_names(&caller, &caller.body.blocks[0]);
        assert!(rebinds(&names, &self_field(&[0])), "case {which}: {names:?}");
    }
}

#[test]
fn a_hand_built_adt_without_a_kind_keeps_the_full_havoc() {
    let untyped = Ty::adt("p::S", vec![("n".into(), u64_ty())]);
    let caller = whole_self_reborrow(untyped);
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(rebinds(&names, &self_field(&[0])), "{names:?}");
}

#[test]
fn a_reborrow_nested_in_an_aggregate_argument_keeps_the_full_havoc() {
    // `f((move _2,))` — a reference inside a tuple is not itself a protected argument.
    let mut caller = whole_self_reborrow(s_ty());
    caller.body.locals.push(LocalDecl {
        index: 4,
        ty: Ty::Tuple(vec![caller.body.locals[2].ty.clone()]),
        name: None,
    });
    caller.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Aggregate(
            trust_types::AggregateKind::Tuple,
            vec![Operand::Move(Place::local(2))],
        ),
        span: SourceSpan::default(),
    });
    caller.body.blocks[0].terminator =
        call_to("p::S::check", vec![Operand::Move(Place::local(4))], 3);
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(rebinds(&names, &self_field(&[0])), "{names:?}");
}

#[test]
fn a_box_field_is_havoced_whole_with_its_heap() {
    // `struct B { b: Box<u64>, n: u64 }`. MIR dereferences a `Box` as a place, so the
    // heap it owns is named `self*.0*` — a descendant of the `Box` field only, not of
    // its `Unique`/`NonNull` pointer leaf. The heap is not covered by `&*self`'s
    // protection; the field must be havoced whole.
    let raw = Ty::RawPtr { mutable: false, pointee: Box::new(u64_ty()) };
    let non_null = extracted_struct("core::ptr::NonNull", vec![("pointer".into(), raw)]);
    let unique = extracted_struct("core::ptr::Unique", vec![("pointer".into(), non_null)]);
    let boxed = extracted_struct("alloc::boxed::Box", vec![("0".into(), unique)]);
    let b = extracted_struct("p::B", vec![("b".into(), boxed), ("n".into(), u64_ty())]);
    let caller = whole_self_reborrow(b);
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(rebinds(&names, "self*.0*"), "the boxed heap must stay havoced: {names:?}");
    assert!(!rebinds(&names, &self_field(&[1])), "the plain `n` beside it is frozen: {names:?}");
}

#[test]
fn a_struct_with_no_recorded_fields_is_havoced_whole() {
    // `struct W { z: Z, n: u64 }` where the extractor recorded no fields for `Z`:
    // nothing proves `Z` has no `UnsafeCell` or pointer under it.
    let z = extracted_struct("p::Z", vec![]);
    let w = extracted_struct("p::W", vec![("z".into(), z), ("n".into(), u64_ty())]);
    let caller = whole_self_reborrow(w);
    let names = terminator_def_names(&caller, &caller.body.blocks[0]);
    assert!(rebinds(&names, &self_field(&[0])), "`z` must stay havoced: {names:?}");
    assert!(rebinds(&names, "self*.0.2"), "and anything projected under it: {names:?}");
    assert!(!rebinds(&names, &self_field(&[1])), "the plain `n` beside it is frozen: {names:?}");
}

// ======================================================================
// UNION-SIBLING-WRITE-2 (2026-10-12): a refined write through a union field
// ======================================================================

/// `fn set_b(r: &mut <two>)` writing `(*r).1 = 1`, and `fn caller(p: &mut <two>)` doing
/// `(*p).0 = 5; set_b(copy p)`. `two` is `union U { a: u32, b: u32 }` or the stamped
/// struct control.
fn union_param_pair(kind: trust_types::AdtKind) -> (VerifiableFunction, VerifiableFunction) {
    let mut two = Ty::adt("p::U", vec![("a".into(), u32_ty()), ("b".into(), u32_ty())]);
    if let Ty::Adt { adt_kind, .. } = &mut two {
        *adt_kind = Some(kind);
    }
    let r = Ty::Ref { mutable: true, inner: Box::new(two) };
    let field =
        |i: usize| Place { local: 1, projections: vec![Projection::Deref, Projection::Field(i)] };
    let body = |stmts: Vec<Statement>, terminator: Terminator, extra: Vec<LocalDecl>| {
        let mut locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: r.clone(), name: Some("p".into()) },
        ];
        locals.extend(extra);
        let mut blocks = vec![BasicBlock { id: BlockId(0), stmts, terminator }];
        if matches!(blocks[0].terminator, Terminator::Call { .. }) {
            blocks.push(BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Return,
            });
        }
        VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        }
    };
    let function = |name: &str, body: VerifiableBody| VerifiableFunction {
        name: name.into(),
        def_path: format!("p::{name}"),
        span: SourceSpan::default(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let store = |i: usize, v: u128| Statement::Assign {
        place: field(i),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(v, 32))),
        span: SourceSpan::default(),
    };
    let helper = function("set_b", body(vec![store(1, 1)], Terminator::Return, vec![]));
    let caller = function(
        "caller",
        body(
            vec![store(0, 5)],
            call_to("p::set_b", vec![Operand::Copy(Place::local(1))], 2),
            vec![LocalDecl { index: 2, ty: Ty::Unit, name: None }],
        ),
    );
    (helper, caller)
}

/// The refinement replaces the root `p` by the caller-side spelling of what the callee
/// writes. When that write goes through a UNION field (`(*r).b = 1`), its spelling
/// `p*.1` rebinds no sibling, and `p`, which did, is the name the refinement drops: so
/// the refined list also carries the write's union cover `p*`. FAILS BEFORE: the refined
/// call kept `p*.0`, the value the callee's write replaced. The STRUCT control keeps
/// `p*.0` (the refinement's point).
#[test]
fn a_refined_call_writing_a_union_field_rebinds_the_siblings() {
    for (kind, union) in
        [(trust_types::AdtKind::Union, true), (trust_types::AdtKind::Struct, false)]
    {
        let (helper, caller) = union_param_pair(kind);
        let ws = derive_callee_write_set(&helper).expect("in-fragment helper");
        let _scope = enter_test_callee_write_sets(map_with("p::set_b", ws));
        let names = terminator_def_names(&caller, &caller.body.blocks[0]);
        assert!(!names.iter().any(|n| n == "p"), "premise: the root `p` is replaced: {names:?}");
        assert!(names.iter().any(|n| n == "p*.1"), "premise: the written field: {names:?}");
        assert_eq!(
            names.iter().any(|n| crate::generate::write_rebinds(n, "p*.0")),
            union,
            "{kind:?}: {names:?}"
        );
    }
}
