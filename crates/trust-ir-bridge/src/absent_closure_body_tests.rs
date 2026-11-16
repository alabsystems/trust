//! CLOSURE-ABSENT-CALLEE (fix6): a `Fn*::call*` shim whose closure body is not in
//! the bundle lowers as an ordinary fail-closed absent callee, and havocs what the
//! closure may write, instead of failing the whole caller.
//!
//! Measured shape (preview4, 7 functions / 214 rows): the closure body is refused by
//! lowering (an owned-sequence gap), the compiler's survivor retry drops it, and the
//! caller's `<{closure} as FnMut>::call_mut` then hard-failed with "closure body is
//! not present in the TrustIr module". These tests pin the replacement:
//!
//! * the caller lowers, with the may-panic marker and one fail-closed absent-callee
//!   `PanicFreedom` row, and no call into a phantom body;
//! * the closure's own body still does not lower, so its own obligations are not
//!   proved, and the survivor probe still drops it while keeping the caller;
//! * a `&mut` capture and a `&mut` argument are havocked before the marker;
//! * a capture whose reach one store cannot cover still fails the caller closed.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir::inst::Inst;
use trust_ir::ty::Ty as TrustIrTy;
use trust_ir::value::ValueId;
use trust_ir_build::validate_module;
use trust_types::{
    AggregateKind, BasicBlock as TrustBlock, BlockId, ClosureCallKind, ConstValue, LocalDecl,
    Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody,
    VerifiableFunction,
};

use crate::lower::{
    BridgeError, lower_to_trust_ir, lower_to_trust_ir_functions,
    verifiable_function_lowers_in_module_context,
};

const CLOSURE: &str = "test::caller::{closure#0}";
const CALL_MUT: &str = "core::ops::function::FnMut::call_mut";

/// The closure environment type as the extractor spells it (`ty_convert`'s
/// `Ty::Closure`), capturing one `&mut capture_pointee`.
fn closure_env(capture_pointee: &Ty) -> Ty {
    Ty::Closure {
        name: CLOSURE.to_string(),
        upvars: vec![Ty::Ref { mutable: true, inner: Box::new(capture_pointee.clone()) }],
        call: None,
    }
}

fn local(index: usize, ty: Ty, name: &str) -> LocalDecl {
    LocalDecl { index, ty, name: Some(name.into()) }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn function(def_path: &str, body: VerifiableBody) -> VerifiableFunction {
    VerifiableFunction {
        name: def_path.rsplit("::").next().unwrap_or(def_path).to_string(),
        def_path: def_path.to_string(),
        span: SourceSpan::default(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `fn caller() -> u32 { let mut x = 0; let mut f = || x += 1; f(); x }`, with an
/// optional `&mut u32` call argument (`f(&mut y)`), and the closure's capture typed
/// `capture_pointee` behind a `&mut`.
///
/// Locals: 0 ret, 1 `x`, 2 `&mut x`, 3 `f`, 4 `&mut f`, 5 args tuple, 6 call
/// result, 7 `y`, 8 `&mut y`.
fn caller(capture_pointee: Ty, with_mut_arg: bool) -> VerifiableFunction {
    let args_tuple_ty = if with_mut_arg {
        Ty::Tuple(vec![Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) }])
    } else {
        Ty::Tuple(vec![])
    };
    let mut stmts = vec![
        assign(Place::local(1), Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32)))),
        assign(Place::local(2), Rvalue::Ref { mutable: true, place: Place::local(1) }),
        assign(
            Place::local(3),
            Rvalue::Aggregate(
                AggregateKind::Closure {
                    name: CLOSURE.to_string(),
                    captures: vec![],
                    call_kind: ClosureCallKind::FnMut,
                },
                vec![Operand::Move(Place::local(2))],
            ),
        ),
        assign(Place::local(4), Rvalue::Ref { mutable: true, place: Place::local(3) }),
    ];
    if with_mut_arg {
        stmts
            .push(assign(Place::local(7), Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32)))));
        stmts.push(assign(Place::local(8), Rvalue::Ref { mutable: true, place: Place::local(7) }));
        stmts.push(assign(
            Place::local(5),
            Rvalue::Aggregate(AggregateKind::Tuple, vec![Operand::Move(Place::local(8))]),
        ));
    } else {
        stmts.push(assign(Place::local(5), Rvalue::Aggregate(AggregateKind::Tuple, vec![])));
    }
    function(
        "test::caller",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                local(1, capture_pointee.clone(), "x"),
                local(
                    2,
                    Ty::Ref { mutable: true, inner: Box::new(capture_pointee.clone()) },
                    "x_ref",
                ),
                local(3, closure_env(&capture_pointee), "f"),
                local(
                    4,
                    Ty::Ref { mutable: true, inner: Box::new(closure_env(&capture_pointee)) },
                    "f_ref",
                ),
                local(5, args_tuple_ty, "args"),
                local(6, Ty::Unit, "unit"),
                local(7, Ty::u32(), "y"),
                local(8, Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) }, "y_ref"),
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts,
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: None,
                        is_foreign: false,
                        func: CALL_MUT.to_string(),
                        args: vec![Operand::Move(Place::local(4)), Operand::Move(Place::local(5))],
                        dest: Place::local(6),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Copy(Place::local(1))),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
    )
}

/// The closure's own body, which lowering REFUSES: it reads a local of a type the
/// bridge cannot model (the stand-in for the owned-sequence gap that refused the
/// measured closures).
fn refused_closure() -> VerifiableFunction {
    let refused = Ty::Unsupported {
        kind: "TyKind::Foreign".into(),
        detail: "opaque foreign type the bridge does not model".into(),
    };
    function(
        CLOSURE,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                local(
                    1,
                    Ty::Ref { mutable: true, inner: Box::new(closure_env(&Ty::u32())) },
                    "self",
                ),
                local(2, refused.clone(), "opaque"),
                local(3, refused, "copy"),
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(2))))],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
    )
}

fn lowers_in_context(bundle: &[VerifiableFunction], index: usize) -> bool {
    let empty: std::collections::HashSet<String> = std::collections::HashSet::new();
    verifiable_function_lowers_in_module_context(bundle, index, &empty, &empty)
}

fn absent_callee_rows(module: &trust_ir::Module) -> Vec<&str> {
    module
        .proof_obligations
        .iter()
        .filter(|o| {
            o.kind == trust_ir::ObligationKind::PanicFreedom
                && o.description
                    .starts_with(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
        })
        .map(|o| o.description.as_str())
        .collect()
}

fn caller_insts(module: &trust_ir::Module) -> Vec<&trust_ir::node::InstrNode> {
    module.functions[0].blocks.iter().flat_map(|b| b.body.iter()).collect()
}

/// A `Store` of a `u32` whose value is a fresh `Undef` havoc.
fn u32_havoc_stores(module: &trust_ir::Module) -> usize {
    let insts = caller_insts(module);
    let havocs: Vec<ValueId> = insts
        .iter()
        .filter(|n| {
            matches!(n.inst, Inst::Undef { ty: TrustIrTy::U32 })
                && n.proofs.contains(&trust_ir::ProofAnnotation::FreshSymbolicHavoc)
        })
        .flat_map(|n| n.results.iter().copied())
        .collect();
    insts
        .iter()
        .filter(|n| {
            matches!(&n.inst, Inst::Store { ty: TrustIrTy::U32, value, .. } if havocs.contains(value))
        })
        .count()
}

fn assert_fail_closed_absent_call(module: &trust_ir::Module) {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "the lowered caller must be a valid module: {errors:?}");
    let insts = caller_insts(module);
    assert!(
        insts.iter().any(|n| {
            matches!(n.inst, Inst::Assert { .. })
                && n.proofs.contains(&trust_ir::ProofAnnotation::NoPanic)
        }),
        "the absent closure call must keep the Assert(false)+NoPanic may-panic marker"
    );
    assert!(
        !insts.iter().any(|n| matches!(n.inst, Inst::Call { .. })),
        "an absent closure body must never become a call into a phantom body"
    );
    let rows = absent_callee_rows(module);
    assert_eq!(rows.len(), 1, "exactly one fail-closed absent-callee row, got {rows:?}");
    assert!(
        rows[0].contains(CLOSURE),
        "the row must name the closure whose body is absent: {}",
        rows[0]
    );
}

/// The caller of a closure whose body is absent now LOWERS (it used to hard-fail
/// with "closure body is not present", losing every row of the caller), and the
/// call is the fail-closed absent callee.
#[test]
fn a_caller_of_an_absent_closure_body_lowers_as_a_fail_closed_absent_call() {
    let module = lower_to_trust_ir(&caller(Ty::u32(), false))
        .expect("the caller must lower with the closure call as an absent callee");
    assert_fail_closed_absent_call(&module);
}

/// The closure's own obligations are not hidden: its refused body still does not
/// lower, so its own verdict cannot be proved, and in the survivor context the
/// probe still DROPS it while the caller is kept and lowers.
#[test]
fn the_absent_closure_itself_is_still_refused_and_never_proved() {
    let closure = refused_closure();
    assert!(lower_to_trust_ir(&closure).is_err(), "the closure's own body must stay refused");

    let bundle = vec![caller(Ty::u32(), false), closure];
    assert!(
        lower_to_trust_ir_functions("test", &bundle).is_err(),
        "the whole bundle still fails, which is what sends the compiler to its survivor retry"
    );
    assert!(lowers_in_context(&bundle, 0), "caller is kept");
    assert!(!lowers_in_context(&bundle, 1), "closure is dropped");

    let survivors = lower_to_trust_ir_functions("test", &bundle[..1])
        .expect("the survivor bundle (the caller alone) must lower");
    assert_eq!(survivors.functions.len(), 1, "the refused closure is not in the module");
    assert_fail_closed_absent_call(&survivors);
}

/// A `&mut` capture is havocked: a fresh value is stored through the captured
/// reference before the marker, so nothing the caller knew about `x` survives the
/// call. Killed by a mutant that skips the capture havoc.
#[test]
fn a_mut_capture_of_an_absent_closure_is_havocked() {
    let module = lower_to_trust_ir(&caller(Ty::u32(), false)).expect("caller lowers");
    assert_eq!(
        u32_havoc_stores(&module),
        1,
        "the `&mut u32` capture must receive exactly one fresh havoc store"
    );
    // The havoc precedes the marker, in the same block.
    let entry = &module.functions[0].blocks[0].body;
    let store = entry
        .iter()
        .position(|n| matches!(n.inst, Inst::Store { ty: TrustIrTy::U32, .. }))
        .expect("store in the entry block");
    let marker = entry
        .iter()
        .rposition(|n| matches!(n.inst, Inst::Assert { .. }))
        .expect("marker in the entry block");
    assert!(store < marker, "the capture havoc must precede the may-panic marker");
}

/// A `&mut` ARGUMENT of the call is havocked too: the closure may write through it.
#[test]
fn a_mut_argument_of_an_absent_closure_call_is_havocked() {
    let module = lower_to_trust_ir(&caller(Ty::u32(), true)).expect("caller lowers");
    assert_fail_closed_absent_call(&module);
    assert_eq!(
        u32_havoc_stores(&module),
        2,
        "both the `&mut` capture and the `&mut` argument must receive a fresh havoc store"
    );
}

/// A capture whose pointee itself holds a reference (`&mut &mut u32`) cannot be
/// covered by one store, so the caller still fails closed, as before.
#[test]
fn a_capture_reaching_further_places_still_fails_the_caller_closed() {
    let nested = Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) };
    let err = lower_to_trust_ir(&caller(nested, false))
        .expect_err("a capture one store cannot cover must keep failing closed");
    assert!(
        matches!(&err, BridgeError::UnsupportedOp(msg)
            if msg.contains("closure body is not present") && msg.contains("capture 0")),
        "expected the capture refusal, got {err:?}"
    );
}
