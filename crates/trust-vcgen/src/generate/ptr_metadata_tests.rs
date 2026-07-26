use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator,
    Ty, UnOp, VcKind, VerifiableBody, VerifiableFunction,
};

use super::unsupported_mir_vcs;

/// SOUNDNESS GATE for the slice-len `isize::MAX` upper bound: it may apply ONLY
/// to provably non-ZST elements (a `&[()]` length can reach `usize::MAX`, so an
/// unconditional bound false-PROVEs `len + k`). Pins the gate.
#[test]
fn slice_len_upper_bound_gate_excludes_zst() {
    use super::ty_is_definitely_non_zst;
    // Provably non-ZST (>= 1 byte): upper bound is sound.
    assert!(ty_is_definitely_non_zst(&Ty::Int { width: 8, signed: false }));
    assert!(ty_is_definitely_non_zst(&Ty::Int { width: 32, signed: false })); // char
    assert!(ty_is_definitely_non_zst(&Ty::Bool));
    assert!(ty_is_definitely_non_zst(&Ty::Ref { mutable: false, inner: Box::new(Ty::Bool) }));
    // Struct/tuple with a non-ZST field is non-ZST (no regression on &[Struct]).
    assert!(ty_is_definitely_non_zst(&Ty::Tuple(vec![Ty::Unit, Ty::Bool])));
    assert!(ty_is_definitely_non_zst(&Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "S".into(),
        fields: vec![("a".into(), Ty::Unit), ("b".into(), Ty::Int { width: 8, signed: false })],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }));
    // ZST or all-ZST: MUST be excluded (no upper bound).
    assert!(!ty_is_definitely_non_zst(&Ty::Unit));
    assert!(!ty_is_definitely_non_zst(&Ty::Tuple(vec![])));
    assert!(!ty_is_definitely_non_zst(&Ty::Tuple(vec![Ty::Unit, Ty::Unit])));
    assert!(!ty_is_definitely_non_zst(&Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "Z".into(),
        fields: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }));
    assert!(!ty_is_definitely_non_zst(&Ty::Array {
        elem: Box::new(Ty::Int { width: 8, signed: false }),
        len: 0,
    }));
}

/// Build `fn f(p: <operand_ty>) { let _2 = PtrMetadata(Copy(_1)); }` so the
/// single statement exercises exactly the `collect_rvalue_unsupported`
/// PtrMetadata arm under test.
fn ptr_metadata_fn(operand_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "ptr_meta".to_string(),
        def_path: "test::ptr_meta".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // return
                LocalDecl { index: 1, ty: operand_ty, name: Some("p".into()) }, // operand
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("len".into()) }, // metadata dest
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Count only `Rvalue::UnaryOp(PtrMetadata)` UnsupportedMir obligations — the
/// type-walk may emit other-kinded VCs for the slice/raw-ptr local type, which
/// this filter deliberately ignores.
fn ptr_metadata_unsupported(func: &VerifiableFunction) -> usize {
    unsupported_mir_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. } if kind == "Rvalue::UnaryOp(PtrMetadata)"
            )
        })
        .count()
}

/// A *recursive* ADT — `clean_kernel::Expr` is the live example: a CIC term
/// (App / Const / Lambda / Pi …) whose fields reference `Expr` again, so
/// trust-mir-extract lowers it to `Ty::Unsupported { kind: "TyKind::Adt",
/// detail: "recursive enum ..." }`.
fn recursive_adt_ty() -> Ty {
    Ty::Unsupported {
        kind: "TyKind::Adt".into(),
        detail: "recursive enum clean_kernel::Expr encountered while lowering variants".into(),
    }
}

/// `fn int_ty() -> Expr { .. }` / `fn noOverflow_app(min, result, max: Expr)
/// -> Expr` shape: every param and the return value `_0` are the recursive
/// `Expr` term, and the body only constructs/returns (no panic-able op). The
/// declaration walk must NOT stamp an `UnsupportedMir` marker — the function
/// must verify cleanly (0 obligations / Proved), not fail closed to Unknown.
#[test]
fn recursive_adt_return_and_params_emit_no_unsupported_vc() {
    let expr = recursive_adt_ty();
    let func = VerifiableFunction {
        name: "noOverflow_app".to_string(),
        def_path: "trust_semantics::noOverflow_app".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: expr.clone(), name: None }, // return _0: Expr
                LocalDecl { index: 1, ty: expr.clone(), name: Some("min".into()) },
                LocalDecl { index: 2, ty: expr.clone(), name: Some("result".into()) },
                LocalDecl { index: 3, ty: expr.clone(), name: Some("max".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty: expr,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let unsupported = unsupported_mir_vcs(&func)
        .into_iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. }))
        .count();
    assert_eq!(
        unsupported, 0,
        "a pure constructor/builder over a recursive ADT (`Expr`) with no \
         panic-able operation must not emit a declaration-level UnsupportedMir \
         marker"
    );
}

/// GUARDRAIL 1 (other unsupported kinds still fail closed): only the
/// recursive-ADT *value-type* case is relaxed. A genuinely-unsupported
/// declaration kind (here an unnormalized `TyKind::Alias`) must STILL emit
/// its declaration-level `UnsupportedMir` marker.
#[test]
fn non_recursive_unsupported_type_still_fails_closed() {
    let alias = Ty::Unsupported {
        kind: "TyKind::Alias".into(),
        detail: "alias type was not normalized".into(),
    };
    let func = VerifiableFunction {
        name: "uses_alias".to_string(),
        def_path: "test::uses_alias".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: alias, name: Some("a".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let unsupported = unsupported_mir_vcs(&func)
        .into_iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "TyKind::Alias")
        })
        .count();
    assert!(
        unsupported >= 1,
        "a genuinely-unsupported (non-recursive-ADT) type declaration must \
         still fail closed with an UnsupportedMir marker"
    );
}

/// GUARDRAIL 2 (a real safety obligation survives the relaxation): a
/// constructor that returns the recursive `Expr` but also performs an
/// unbounded `x + y` (u32 `Add`) in its body MUST still emit the
/// `ArithmeticOverflow` VC. Relaxing the recursive-ADT *declaration* marker
/// must never swallow a genuine use-site safety obligation.
#[test]
fn recursive_adt_constructor_with_inner_overflow_still_emits_overflow_vc() {
    use trust_types::{BinOp, Operand, Rvalue};

    use super::generate_vcs;
    let expr = recursive_adt_ty();
    let func = VerifiableFunction {
        name: "mk_with_add".to_string(),
        def_path: "test::mk_with_add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: expr.clone(), name: None }, // return _0: Expr
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("sum".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: expr,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "an unbounded `x + y` inside a recursive-ADT-returning constructor MUST \
         still emit an ArithmeticOverflow obligation: {vcs:#?}"
    );
}

/// A `TyKind::Param` — the polymorphic-MIR appearance of a generic parameter
/// `T` (e.g. the `_items: &[T]` element type of `fn g<T>(_items: &[T], x:
/// u32)`). trust-mir-extract lowers it to `Ty::Unsupported { kind:
/// "TyKind::Param", … }`.
fn generic_param_ty() -> Ty {
    Ty::Unsupported {
        kind: "TyKind::Param".into(),
        detail: "generic parameter T/#0 needs monomorphization".into(),
    }
}

/// `fn g<T>(_items: &[T], …) -> …` shape where the generic parameter appears
/// ONLY in declarations (a forwarded/unused param + the return), never in a
/// panic-able operation. The declaration walk must NOT stamp an
/// `UnsupportedMir` marker: the function must be free to prove panic-free for
/// ALL T w.r.t. its T-independent obligations, not fail closed to Unknown on
/// the `T`-typed declaration alone.
#[test]
fn generic_param_declaration_emits_no_unsupported_vc() {
    let t = generic_param_ty();
    let func = VerifiableFunction {
        name: "g_total_guarded".to_string(),
        def_path: "test::g_total_guarded".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: t.clone(), name: None }, // return _0: T
                LocalDecl { index: 1, ty: t.clone(), name: Some("items".into()) },
                LocalDecl { index: 2, ty: t, name: Some("item".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: generic_param_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let unsupported = unsupported_mir_vcs(&func)
        .into_iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. }))
        .count();
    assert_eq!(
        unsupported, 0,
        "a generic parameter `T` appearing only in type declarations carries no \
         safety obligation and must not emit a declaration-level UnsupportedMir marker"
    );
}

/// GUARDRAIL (the relaxation is narrow / Param-specific): suppressing the
/// `Param` declaration marker must NOT suppress markers for genuinely
/// unsupported types. A function carrying BOTH a `Param` local (relaxed) and
/// an unnormalized `TyKind::Alias` local (still unsupported) in the SAME
/// declaration walk must emit exactly the Alias marker and NOT a Param one —
/// proving the relaxation did not over-fire.
///
/// (The structural soundness guarantee is separate and stronger: a `Param`
/// value can never be the operand of a primitive arithmetic/bounds/div VC —
/// Rust lowers `a + b` for generic `T: Add` to a *call* `<T as Add>::add`,
/// never to `Rvalue::BinaryOp` — so a relaxed `Param` declaration can never
/// hide a primitive panic obligation. See `sort_for_ty`/`Sort::from_ty`: a
/// `Param` local is modeled as a benign `Int`-sorted symbolic value.)
#[test]
fn generic_param_relaxation_is_param_specific() {
    let t = generic_param_ty();
    let alias = Ty::Unsupported {
        kind: "TyKind::Alias".into(),
        detail: "alias type was not normalized".into(),
    };
    let func = VerifiableFunction {
        name: "param_and_alias".to_string(),
        def_path: "test::param_and_alias".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: t, name: Some("t".into()) }, // relaxed
                LocalDecl { index: 2, ty: alias, name: Some("a".into()) }, // still stamps
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let markers: Vec<String> = unsupported_mir_vcs(&func)
        .into_iter()
        .filter_map(|vc| match vc.kind {
            VcKind::UnsupportedMir { kind, .. } => Some(kind),
            _ => None,
        })
        .collect();
    assert!(
        markers.iter().any(|k| k == "TyKind::Alias"),
        "a genuinely-unsupported `TyKind::Alias` declaration must still stamp its \
         marker: {markers:?}"
    );
    assert!(
        !markers.iter().any(|k| k == "TyKind::Param"),
        "the relaxed `TyKind::Param` declaration must NOT stamp a marker: {markers:?}"
    );
}

/// GUARDRAIL (a real obligation survives the relaxation): a generic function
/// `fn g<T>(_items: &[T], x: u32, y: u32)` whose body performs an unbounded
/// `x + y` (u32 `Add`) MUST still emit the `ArithmeticOverflow` VC. Relaxing
/// the `Param` *declaration* marker must never swallow a genuine T-independent
/// safety obligation (this is the `g_panic_sub<T>` / `g_total_guarded<T>`
/// case at the unit level).
#[test]
fn generic_function_inner_overflow_still_emits_overflow_vc() {
    use trust_types::{BinOp, Operand, Rvalue};

    use super::generate_vcs;
    let t = generic_param_ty();
    let func = VerifiableFunction {
        name: "g_add".to_string(),
        def_path: "test::g_add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // return _0: u32
                LocalDecl { index: 1, ty: t, name: Some("items".into()) }, // _1: &[T]-ish
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("sum".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(2)),
                        Operand::Copy(Place::local(3)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "an unbounded `x + y` inside a generic function MUST still emit an \
         ArithmeticOverflow obligation despite the relaxed `Param` declaration \
         marker: {vcs:#?}"
    );
}

/// An `[T; N]` whose length is not a concrete `usize` (generic-const /
/// unevaluated-const length) lowers to `Ty::Unsupported { kind:
/// "TyKind::Array", … }`.
fn unmodeled_array_ty() -> Ty {
    Ty::Unsupported {
        kind: "TyKind::Array".into(),
        detail: "array length UnevaluatedConst { .. } is not a concrete target usize".into(),
    }
}

/// A function whose locals are unmodeled-length arrays (only in declarations)
/// must NOT stamp a declaration-level `UnsupportedMir` marker — a value of an
/// unmodeled array type carries no obligation by itself; an actual index
/// fails closed independently via its `bounds` VC.
#[test]
fn unmodeled_array_declaration_emits_no_unsupported_vc() {
    let arr = unmodeled_array_ty();
    let func = VerifiableFunction {
        name: "holds_unmodeled_array".to_string(),
        def_path: "test::holds_unmodeled_array".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u8(), name: None },
                LocalDecl { index: 1, ty: arr.clone(), name: Some("arr".into()) },
                LocalDecl { index: 2, ty: arr, name: Some("other".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let unsupported = unsupported_mir_vcs(&func)
        .into_iter()
        .filter(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. }))
        .count();
    assert_eq!(
        unsupported, 0,
        "an unmodeled-length array appearing only in type declarations carries no \
         safety obligation and must not emit a declaration-level UnsupportedMir marker"
    );
}

/// GUARDRAIL (the relaxation is array-specific): an unmodeled `TyKind::Array`
/// is relaxed, but a genuinely-unsupported `TyKind::Alias` in the SAME function
/// must STILL stamp its marker — the relaxation did not over-fire.
#[test]
fn unmodeled_array_relaxation_is_array_specific() {
    let arr = unmodeled_array_ty();
    let alias = Ty::Unsupported {
        kind: "TyKind::Alias".into(),
        detail: "alias type was not normalized".into(),
    };
    let func = VerifiableFunction {
        name: "array_and_alias".to_string(),
        def_path: "test::array_and_alias".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: arr, name: Some("arr".into()) }, // relaxed
                LocalDecl { index: 2, ty: alias, name: Some("a".into()) }, // still stamps
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let markers: Vec<String> = unsupported_mir_vcs(&func)
        .into_iter()
        .filter_map(|vc| match vc.kind {
            VcKind::UnsupportedMir { kind, .. } => Some(kind),
            _ => None,
        })
        .collect();
    assert!(
        markers.iter().any(|k| k == "TyKind::Alias"),
        "a genuinely-unsupported `TyKind::Alias` declaration must still stamp: {markers:?}"
    );
    assert!(
        !markers.iter().any(|k| k == "TyKind::Array"),
        "the relaxed `TyKind::Array` declaration must NOT stamp a marker: {markers:?}"
    );
}

#[test]
fn slice_ref_ptr_metadata_emits_no_unsupported_vc() {
    // `&[u32]`: the fat-pointer length is modeled by `slice_len_formula`, so
    // the spurious obligation must be suppressed (the `s.len()` bounds idiom).
    let func = ptr_metadata_fn(Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
    });
    assert_eq!(
        ptr_metadata_unsupported(&func),
        0,
        "PtrMetadata over &[u32] is modeled by slice_len_formula and must not \
         emit an UnsupportedMir obligation"
    );
}

#[test]
fn raw_ptr_ptr_metadata_still_fails_closed() {
    // `*const u32`: `slice_len_formula` returns None (no fat-pointer length
    // semantics), so the obligation must still fail closed to Unknown.
    let func = ptr_metadata_fn(Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) });
    assert_eq!(
        ptr_metadata_unsupported(&func),
        1,
        "PtrMetadata over a raw pointer is unmodelable and must still emit \
         exactly one UnsupportedMir obligation"
    );
}

// ----------------------------------------------------------------------
// Problem B: infallible slice->array `try_into().unwrap()` suppression.
// ----------------------------------------------------------------------

use trust_types::{AggregateKind, ConstValue};

/// Count `Call::unwrap::panic-freedom-unverified` UnsupportedMir obligations.
fn unwrap_panic_freedom_count(func: &VerifiableFunction) -> usize {
    unsupported_mir_vcs(func)
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "Call::unwrap::panic-freedom-unverified")
        })
        .count()
}

/// `usize` Range aggregate operand.
fn ci(v: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(v, 64))
}

/// Build the REAL MIR chain `u64::from_le_bytes(bytes[start..end].try_into().unwrap())`:
///   _2 = Range { start, end }                            (aggregate)
///   _3 = <[u8] as Index<Range>>::index(move bytes, _2)   (-> &[u8])
///   _4 = <&[u8] as TryInto<[u8; arr_len]>>::try_into(_3) (-> Result<[u8;N],_>)
///   _5 = Result::unwrap(move _4)                         (-> [u8; arr_len])
/// `result_ty` lets a test inject a non-array `_5`/`_4` to exercise declines.
fn try_into_unwrap_fn(
    start: u128,
    end: u128,
    arr_len: u64,
    result_ty: Ty,
) -> VerifiableFunction {
    let arr = Ty::Array { elem: Box::new(Ty::Int { width: 8, signed: false }), len: arr_len };
    let slice_ref =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    let range_ty = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "core::ops::Range".into(),
        fields: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    VerifiableFunction {
        name: "hashy".into(),
        def_path: "test::hashy".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None }, // _0 ret
                LocalDecl { index: 1, ty: slice_ref.clone(), name: Some("bytes".into()) }, // _1
                LocalDecl { index: 2, ty: range_ty, name: None },  // _2 range
                LocalDecl { index: 3, ty: slice_ref, name: None }, // _3 &[u8]
                LocalDecl { index: 4, ty: result_ty, name: None }, // _4 Result<[u8;N],_>
                LocalDecl { index: 5, ty: arr, name: None },       // _5 [u8;N]
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "core::ops::Range".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![ci(start), ci(end)],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::ops::index::Index::index".into(),
                        args: vec![
                            Operand::Move(Place::local(1)),
                            Operand::Move(Place::local(2)),
                        ],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::convert::TryInto::try_into".into(),
                        args: vec![Operand::Move(Place::local(3))],
                        dest: Place::local(4),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::result::Result::<T, E>::unwrap".into(),
                        args: vec![Operand::Move(Place::local(4))],
                        dest: Place::local(5),
                        target: Some(BlockId(3)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn result_array(n: u64) -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "core::result::Result".into(),
        fields: vec![
            ("0".into(), Ty::Array { elem: Box::new(Ty::u8()), len: n }),
            ("1".into(), Ty::Unit),
        ],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

/// The targeted PROOF: `bytes[0..8].try_into().unwrap()` into `[u8; 8]` from a
/// length-8 constant range is INFALLIBLE, so NO panic-freedom obligation.
#[test]
fn const_range_try_into_unwrap_is_suppressed() {
    let func = try_into_unwrap_fn(0, 8, 8, result_array(8));
    assert_eq!(
        unwrap_panic_freedom_count(&func),
        0,
        "a length-8 constant `bytes[0..8]` -> `[u8;8]` try_into().unwrap() is \
         infallible and must NOT emit a panic-freedom obligation"
    );
}

/// SOUNDNESS GATE: a WRONG-length constant range (`bytes[0..7]` into `[u8; 8]`)
/// is genuinely fallible — the unwrap CAN panic — so the obligation MUST stay.
#[test]
fn wrong_length_const_range_try_into_unwrap_is_flagged() {
    let func = try_into_unwrap_fn(0, 7, 8, result_array(8));
    assert_eq!(
        unwrap_panic_freedom_count(&func),
        1,
        "a length-7 range into [u8;8] is fallible; the unwrap obligation must remain"
    );
}

/// SOUNDNESS GATE: a RUNTIME-VARIABLE range (modeled here by replacing the
/// constant `Range` aggregate with a non-constant start) has NO static length,
/// so the conversion is not provably infallible and the obligation MUST stay.
/// This pins the `bytes[len-8..]` / `bytes[off..off+8]` behavior — never proved
/// away without a static length equality.
#[test]
fn runtime_range_try_into_unwrap_is_flagged() {
    let mut func = try_into_unwrap_fn(0, 8, 8, result_array(8));
    // Overwrite _2's Range with a non-constant `end` (Copy of a local).
    if let Statement::Assign { rvalue, .. } = &mut func.body.blocks[0].stmts[0] {
        *rvalue = Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "core::ops::Range".into(),
                variant: 0,
                active_field: None,
                args: None,
            },
            vec![ci(0), Operand::Copy(Place::local(1))],
        );
    }
    assert_eq!(
        unwrap_panic_freedom_count(&func),
        1,
        "a runtime-variable range has no static length; the unwrap stays flagged"
    );
}

/// SOUNDNESS GATE: an ARBITRARY `Result::unwrap` whose receiver is NOT a
/// slice->array conversion (here the receiver is a plain function-returned
/// `Result`) must STILL be flagged.
#[test]
fn arbitrary_result_unwrap_is_still_flagged() {
    let func = VerifiableFunction {
        name: "plain".into(),
        def_path: "test::plain".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Adt { adt_kind: None, layout: None, 
                        variants: Vec::new(),
                        name: "core::result::Result".into(),
                        fields: vec![("0".into(), Ty::u64()), ("1".into(), Ty::Unit)],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, },
                    name: None,
                },
                LocalDecl { index: 2, ty: Ty::u64(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "mycrate::fallible".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::result::Result::<T, E>::unwrap".into(),
                        args: vec![Operand::Move(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert_eq!(
        unwrap_panic_freedom_count(&func),
        1,
        "an arbitrary Result::unwrap (not a slice->array conversion) must stay flagged"
    );
}

/// SOUNDNESS GATE (hostile review, Attack 1): a USER `impl Index<Range<usize>,
/// Output = [u8]>` renders as the SAME `core::ops::index::Index::index` trait
/// path as the built-in slice impl, yet may return a slice of ANY length — so
/// `w[0..8].try_into::<[u8; 8]>().unwrap()` can PANIC. The receiver-type guard
/// declines (receiver is a user ADT `MyWrap`, not a slice/array), so the
/// obligation MUST stay flagged. Without the guard this was a FALSE PROVE.
#[test]
fn user_index_impl_const_range_try_into_unwrap_is_flagged() {
    let mut func = try_into_unwrap_fn(0, 8, 8, result_array(8));
    // Retype the index RECEIVER local `_1` from `&[u8]` to a user ADT `&MyWrap`.
    func.body.locals[1].ty = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "mycrate::MyWrap".into(),
            fields: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, }),
    };
    assert_eq!(
        unwrap_panic_freedom_count(&func),
        1,
        "a user Index<Range> impl returns an arbitrary-length slice; the \
         unwrap CAN panic and the obligation MUST stay flagged"
    );
}

// ----------------------------------------------------------------------
// Part A: RangeFrom `bytes[len-K..]` static-length recovery (case (d)).
// Part B: hardened `Result::unwrap` twin suppression iff infallible.
// ----------------------------------------------------------------------

/// Build the REAL MIR chain `u64::from_le_bytes(bytes[len - K..].try_into().unwrap())`
/// matching the dumped `hash_bytes` shape:
///   _2 = PtrMetadata(Copy(_1))                 (slice length `bytes.len()`)
///   _8 = CheckedSub(Copy(_2), const K)         (`len - K`, value in field 0)
///   _7 = Use(Move(_8.0))                       (the `len - K` value)
///   _6 = RangeFrom { start: Move(_7) }
///   _5 = Index::index(Copy(_1), Move(_6))      (-> &[u8])
///   _4 = TryInto::try_into(Move(_5))           (-> Result<[u8; arr_len], _>)
///   _3 = Result::unwrap(Move(_4))              (-> [u8; arr_len])
/// `len_recv` selects the slice whose `PtrMetadata` defines `_2` (defaults to the
/// indexed receiver `_1`; a test passes a DIFFERENT local to exercise the
/// other-slice decline). `sub_k` is the constant subtracted in `len - sub_k`.
fn rangefrom_suffix_fn(sub_k: u128, arr_len: u64, len_recv: usize) -> VerifiableFunction {
    use trust_types::BinOp;
    let arr = Ty::Array { elem: Box::new(Ty::u8()), len: arr_len };
    let slice_ref =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    let rangefrom_ty = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "core::ops::RangeFrom".into(),
        fields: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let usize_ty = Ty::Int { width: 64, signed: false };
    let checked_sub_ty = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "(usize, bool)".into(),
        fields: vec![("0".into(), usize_ty.clone()), ("1".into(), Ty::Bool)],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    VerifiableFunction {
        name: "suffix".into(),
        def_path: "test::suffix".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None }, // _0 ret
                LocalDecl { index: 1, ty: slice_ref.clone(), name: Some("bytes".into()) }, // _1
                LocalDecl { index: 2, ty: usize_ty.clone(), name: Some("len".into()) }, // _2 len
                LocalDecl { index: 3, ty: arr, name: None }, // _3 [u8;N]
                LocalDecl { index: 4, ty: result_array(arr_len), name: None }, // _4 Result
                LocalDecl { index: 5, ty: slice_ref.clone(), name: None }, // _5 &[u8]
                LocalDecl { index: 6, ty: rangefrom_ty, name: None }, // _6 RangeFrom
                LocalDecl { index: 7, ty: usize_ty, name: None }, // _7 len-K value
                LocalDecl { index: 8, ty: checked_sub_ty, name: None }, // _8 (val, ovf)
                // _9: an extra slice, used as the "other slice" length source.
                LocalDecl { index: 9, ty: slice_ref, name: Some("other".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // _2 = PtrMetadata(Copy(_len_recv))  (slice length)
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::UnaryOp(
                                UnOp::PtrMetadata,
                                Operand::Copy(Place::local(len_recv)),
                            ),
                            span: SourceSpan::default(),
                        },
                        // _8 = CheckedSub(Copy(_2), const K)
                        Statement::Assign {
                            place: Place::local(8),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(2)),
                                ci(sub_k),
                            ),
                            span: SourceSpan::default(),
                        },
                        // _7 = Use(Move(_8.0))
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::Use(Operand::Move(Place {
                                local: 8,
                                projections: vec![trust_types::Projection::Field(0)],
                            })),
                            span: SourceSpan::default(),
                        },
                        // _6 = RangeFrom { start: Move(_7) }
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: "core::ops::RangeFrom".into(),
                                    variant: 0,
                                    active_field: None,
                                    args: None,
                                },
                                vec![Operand::Move(Place::local(7))],
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::ops::index::Index::index".into(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Move(Place::local(6)),
                        ],
                        dest: Place::local(5),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::convert::TryInto::try_into".into(),
                        args: vec![Operand::Move(Place::local(5))],
                        dest: Place::local(4),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::result::Result::<T, E>::unwrap".into(),
                        args: vec![Operand::Move(Place::local(4))],
                        dest: Place::local(3),
                        target: Some(BlockId(3)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// PART A — PROOF: `bytes[len - 8..].try_into::<[u8; 8]>().unwrap()` where
/// `len = bytes.len()` recovers a CONSTANT length 8 (== `len - (len - 8)`), so
/// the unwrap is INFALLIBLE and NO panic-freedom obligation is emitted.
#[test]
fn rangefrom_len_minus_k_proves() {
    use super::slice_arg_static_len;
    let func = rangefrom_suffix_fn(8, 8, 1);
    assert_eq!(
        slice_arg_static_len(&func, &Place::local(5), 8),
        Some(8),
        "RangeFrom `bytes[len-8..]` (start = Len(bytes) - 8) has static length 8"
    );
    assert_eq!(
        unwrap_panic_freedom_count(&func),
        0,
        "`bytes[len-8..]` -> `[u8;8]` try_into().unwrap() is infallible; no obligation"
    );
}

/// PART A — the `len - 4` / `[u8; 4]` variant (lib.rs:176 `bytes[len-4..]`).
#[test]
fn rangefrom_len_minus_4_proves() {
    use super::slice_arg_static_len;
    let func = rangefrom_suffix_fn(4, 4, 1);
    assert_eq!(slice_arg_static_len(&func, &Place::local(5), 8), Some(4));
    assert_eq!(unwrap_panic_freedom_count(&func), 0);
}

/// PART A SOUNDNESS GATE: a length/array MISMATCH (`bytes[len-7..]` into
/// `[u8; 8]`) recovers static length 7 != 8, so the conversion is genuinely
/// fallible and the unwrap obligation MUST stay.
#[test]
fn rangefrom_len_mismatch_is_flagged() {
    let func = rangefrom_suffix_fn(7, 8, 1);
    assert_eq!(
        unwrap_panic_freedom_count(&func),
        1,
        "static length 7 != array length 8; the unwrap CAN panic — obligation stays"
    );
}

/// PART A SOUNDNESS GATE: a RangeFrom whose `start` is `Len(OTHER) - K` for a
/// DIFFERENT slice than the one being indexed has NO provable relation to the
/// indexed slice's length, so `s.len() - start` is NOT statically `K`. The
/// place-equality check declines and the obligation MUST stay.
#[test]
fn rangefrom_unknown_len_declines() {
    use super::slice_arg_static_len;
    // _2 = PtrMetadata(_9) (the OTHER slice), but the index receiver is _1.
    let func = rangefrom_suffix_fn(8, 8, 9);
    assert_eq!(
        slice_arg_static_len(&func, &Place::local(5), 8),
        None,
        "RangeFrom start derived from a DIFFERENT slice's length is not provably \
         `Len(receiver) - K`; decline"
    );
    assert_eq!(
        unwrap_panic_freedom_count(&func),
        1,
        "unknown relation to the indexed slice's length; the unwrap stays flagged"
    );
}

/// Count hardened `PanicBoundary` twins whose callee is `Result::unwrap`.
fn hardened_unwrap_twin_count(func: &VerifiableFunction) -> usize {
    crate::hardened::generate_hardened_vcs_for_profile(func)
        .iter()
        .filter(|vc| {
            matches!(&vc.kind,
                VcKind::HardenedBoundary {
                    category: trust_types::HardenedVcCategory::PanicBoundary,
                    callee,
                    ..
                } if super::method_tail(callee) == "unwrap")
        })
        .count()
}

/// PART B — PROOF: the hardened `Result::unwrap` twin is SUPPRESSED for an
/// infallible `bytes[len-8..]` try_into().unwrap() (same predicate as Part A).
#[test]
fn hardened_unwrap_twin_suppressed_when_infallible() {
    let func = rangefrom_suffix_fn(8, 8, 1);
    assert_eq!(
        hardened_unwrap_twin_count(&func),
        0,
        "an infallible slice->array unwrap must NOT emit a hardened PanicBoundary twin"
    );
}

/// PART B SOUNDNESS GATE: a genuinely-fallible unwrap (length/array MISMATCH —
/// `bytes[len-7..]` into `[u8; 8]`) MUST still emit the hardened twin.
#[test]
fn hardened_unwrap_twin_emitted_when_fallible() {
    let func = rangefrom_suffix_fn(7, 8, 1);
    assert_eq!(
        hardened_unwrap_twin_count(&func),
        1,
        "a fallible unwrap (length 7 != [u8;8]) MUST still emit the hardened twin"
    );
}

/// PART B SOUNDNESS GATE: an ARBITRARY `Result::unwrap` (receiver is a plain
/// function-returned Result, NOT a slice->array conversion) MUST still emit the
/// hardened twin — the suppression is exactly as narrow as the Part A predicate.
#[test]
fn hardened_unwrap_twin_emitted_for_arbitrary_unwrap() {
    let func = arbitrary_result_unwrap_fn();
    assert_eq!(
        hardened_unwrap_twin_count(&func),
        1,
        "a non-try_into Result::unwrap is genuinely fallible; the twin MUST stay"
    );
}

/// `mycrate::fallible() -> Result<u64,_>; _2 = _1.unwrap()` — a plain fallible
/// unwrap with no slice->array provenance (shared by Part B gate above).
fn arbitrary_result_unwrap_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "plain".into(),
        def_path: "test::plain".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Adt { adt_kind: None, layout: None, 
                        variants: Vec::new(),
                        name: "core::result::Result".into(),
                        fields: vec![("0".into(), Ty::u64()), ("1".into(), Ty::Unit)],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, },
                    name: None,
                },
                LocalDecl { index: 2, ty: Ty::u64(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "mycrate::fallible".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::result::Result::<T, E>::unwrap".into(),
                        args: vec![Operand::Move(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}
