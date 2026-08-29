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
fn g_ty() -> Ty {
    Ty::adt(
        "p::G",
        vec![(
            "storage".into(),
            Ty::adt("p::Storage", vec![("flag".into(), Ty::Bool), ("other".into(), u32_ty())]),
        )],
    )
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
