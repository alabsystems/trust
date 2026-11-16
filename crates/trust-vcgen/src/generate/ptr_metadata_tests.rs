use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue, Sort, SourceSpan,
    Statement, Terminator, Ty, UnOp, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
};

use super::unsupported_mir_vcs;
use crate::{VcgenError, generate_vcs, try_generate_vcs, validate_function};

fn assert_ptr_metadata_malformed_fails_closed(func: &VerifiableFunction) {
    assert!(try_generate_vcs(func).is_err());
    let vcs = generate_vcs(func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(
        &vcs[0].kind,
        VcKind::UnsupportedMir { kind, .. } if kind == "MalformedTrustIr"
    ));
}

/// SOUNDNESS GATE for the slice-len `isize::MAX` upper bound: it may apply ONLY
/// to provably non-ZST elements (a `&[()]` length can reach `usize::MAX`, so an
/// unconditional bound false-PROVEs `len + k`). Pins the gate.
#[test]
fn slice_len_upper_bound_gate_excludes_zst() {
    use trust_types::alloc_model::ty_is_definitely_nonzero_sized as ty_is_definitely_non_zst;
    // Provably non-ZST (>= 1 byte): upper bound is sound.
    assert!(ty_is_definitely_non_zst(&Ty::Int { width: 8, signed: false }));
    assert!(ty_is_definitely_non_zst(&Ty::Int { width: 32, signed: false })); // char
    assert!(ty_is_definitely_non_zst(&Ty::Char));
    assert!(ty_is_definitely_non_zst(&Ty::PtrSizedInt { signed: false }));
    assert!(ty_is_definitely_non_zst(&Ty::Bool));
    assert!(ty_is_definitely_non_zst(&Ty::Ref { mutable: false, inner: Box::new(Ty::Bool) }));
    // Struct/tuple with a non-ZST field is non-ZST (no regression on &[Struct]).
    assert!(ty_is_definitely_non_zst(&Ty::Tuple(vec![Ty::Unit, Ty::Bool])));
    assert!(ty_is_definitely_non_zst(&Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        variants: Vec::new().into(),
        name: "S".into(),
        fields: vec![("a".into(), Ty::Unit), ("b".into(), Ty::Int { width: 8, signed: false })]
            .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    }));
    // ZST or all-ZST: MUST be excluded (no upper bound).
    assert!(!ty_is_definitely_non_zst(&Ty::Unit));
    assert!(!ty_is_definitely_non_zst(&Ty::Tuple(vec![])));
    assert!(!ty_is_definitely_non_zst(&Ty::Tuple(vec![Ty::Unit, Ty::Unit])));
    assert!(!ty_is_definitely_non_zst(&Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        variants: Vec::new().into(),
        name: "Z".into(),
        fields: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    }));
    assert!(!ty_is_definitely_non_zst(&Ty::Array {
        elem: Box::new(Ty::Int { width: 8, signed: false }),
        len: 0,
    }));
}

// ZST-ENUM-SLICE-LEN-1 (2026-10-11). The extractor renders an enum with a
// flattened `fields` view whose FIRST entry is a synthetic `__tag: isize`, plus a
// per-variant `variants` list. The old predicate read only `fields`, so the
// `__tag` made EVERY enum non-ZST and a `&[One]` (`enum One { A }`, a ZST) took the
// `len <= isize::MAX` ceiling: `a.len() * 2` was proved, kernel-certified and its
// overflow check elided. These helpers build the extractor's own shape
// (`trust_mir_extract::ty_convert::lower_enum_adt`: `__tag` first, then
// `__v{variant}_{field}`, `adt_kind: Some(Enum)`, `layout: None` on the verifier
// lane). The table below is mirrored row for row in
// `trust_ir_bridge::lower::native_len_bound_tests::non_zst_table_mirrors_trust_vcgen`.

fn zst_enum_adt(name: &str, variants: Vec<(&str, Vec<Ty>)>) -> Ty {
    let mut fields = vec![("__tag".to_string(), Ty::Int { width: 64, signed: true })];
    let mut defs = Vec::new();
    for (v_idx, (v_name, v_fields)) in variants.into_iter().enumerate() {
        let named: Vec<(String, Ty)> =
            v_fields.into_iter().enumerate().map(|(i, t)| (i.to_string(), t)).collect();
        for (f_name, t) in &named {
            fields.push((format!("__v{v_idx}_{f_name}"), t.clone()));
        }
        defs.push(trust_types::VariantDef {
            name: v_name.to_string(),
            discriminant: v_idx as i128,
            fields: named,
        });
    }
    Ty::Adt {
        name: name.into(),
        fields: fields.into(),
        variants: defs.into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        arbitrary_precision: None,
        validity_wrapper: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(trust_types::AdtKind::Enum),
    }
}

fn zst_struct_adt(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    Ty::Adt {
        name: name.into(),
        fields: fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect::<Vec<_>>().into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        arbitrary_precision: None,
        validity_wrapper: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(trust_types::AdtKind::Struct),
    }
}

fn with_layout_size(ty: Ty, size: u64) -> Ty {
    let Ty::Adt {
        name,
        fields,
        variants,
        disc_index_safe,
        faithful_enum_repr,
        arbitrary_precision,
        validity_wrapper,
        enum_layout,
        adt_kind,
        ..
    } = ty
    else {
        panic!("with_layout_size takes a Ty::Adt");
    };
    Ty::Adt {
        name,
        fields,
        variants,
        disc_index_safe,
        faithful_enum_repr,
        arbitrary_precision,
        validity_wrapper,
        layout: Some(Box::new(trust_types::AdtLayoutInfo {
            size,
            align: 1,
            field_offsets: Vec::new(),
            repr: "rust".into(),
        })),
        enum_layout,
        adt_kind,
    }
}

/// `core::convert::Infallible` as the extractor renders it: an enum with no
/// variant, whose flattened view is the lone `__tag`.
fn zst_infallible() -> Ty {
    zst_enum_adt("core::convert::Infallible", vec![])
}

/// `(label, ty, expected ty_is_definitely_non_zst)`. Every `false` row is a ZST
/// (or, for `repr_u8_one_variant_unstamped`, a shape the verifier lane cannot
/// size); every `true` row is at least one byte.
fn zst_enum_non_zst_table() -> Vec<(&'static str, Ty, bool)> {
    let u8_ = Ty::Int { width: 8, signed: false };
    let u32_ = Ty::Int { width: 32, signed: false };
    let param = Ty::Unsupported {
        kind: "TyKind::Param".into(),
        detail: "generic parameter T/#0 needs monomorphization".into(),
    };
    let one = zst_enum_adt("One", vec![("A", vec![])]);
    let rep = zst_enum_adt("Rep", vec![("A", vec![])]);
    let wrap = zst_struct_adt("Wrap", vec![("x", one.clone())]);
    vec![
        // ZSTs. Each was `true` before the fix (the `__tag` field).
        ("one_variant", one.clone(), false),
        ("one_variant_unit_payload", zst_enum_adt("OneP", vec![("A", vec![Ty::Unit])]), false),
        (
            "uninhabited_second",
            zst_enum_adt("Two", vec![("A", vec![]), ("B", vec![zst_infallible()])]),
            false,
        ),
        (
            "option_infallible",
            zst_enum_adt(
                "core::option::Option<core::convert::Infallible>",
                vec![("None", vec![]), ("Some", vec![zst_infallible()])],
            ),
            false,
        ),
        (
            "option_generic",
            zst_enum_adt("core::option::Option<T>", vec![("None", vec![]), ("Some", vec![param])]),
            false,
        ),
        ("wrapped", wrap.clone(), false),
        ("tuple_of_zst_enum", Ty::Tuple(vec![one.clone(), Ty::Unit]), false),
        ("array_of_zst_enum", Ty::Array { elem: Box::new(one.clone()), len: 4 }, false),
        ("infallible", zst_infallible(), false),
        (
            "unstamped_variantless",
            Ty::Adt {
                name: "Void".into(),
                fields: vec![("__tag".to_string(), Ty::Int { width: 64, signed: true })].into(),
                variants: Vec::new().into(),
                disc_index_safe: false,
                faithful_enum_repr: None,
                arbitrary_precision: None,
                validity_wrapper: None,
                layout: None,
                enum_layout: None,
                adt_kind: None,
            },
            false,
        ),
        ("wrapped_layout_zero", with_layout_size(wrap, 0), false),
        // The accepted capability cost: `#[repr(u8)] enum Rep { A }` is one byte,
        // but the verifier lane stamps no enum layout, so it is not provably sized.
        ("repr_u8_one_variant_unstamped", rep.clone(), false),
        ("zero_width_bv", Ty::Bv(0), false),
        // At least one byte.
        ("two_variant_fieldless", zst_enum_adt("Real", vec![("A", vec![]), ("B", vec![])]), true),
        (
            "three_variant_fieldless",
            zst_enum_adt(
                "core::cmp::Ordering",
                vec![("Less", vec![]), ("Equal", vec![]), ("Greater", vec![])],
            ),
            true,
        ),
        (
            "option_u32",
            zst_enum_adt("core::option::Option<u32>", vec![("None", vec![]), ("Some", vec![u32_])]),
            true,
        ),
        ("repr_u8_one_variant_stamped", with_layout_size(rep, 1), true),
        (
            "struct_with_sized_field",
            zst_struct_adt("S", vec![("a", Ty::Unit), ("b", u8_.clone())]),
            true,
        ),
        ("tuple_of_zst_enum_and_u8", Ty::Tuple(vec![one, u8_.clone()]), true),
        ("vec", Ty::Seq { elem: Box::new(Ty::Unit), drop_auth: None }, true),
        ("u8", u8_, true),
    ]
}

#[test]
fn slice_len_upper_bound_gate_excludes_zst_enums() {
    use super::ty_is_definitely_non_zst;
    let mut wrong = Vec::new();
    for (label, ty, expected) in zst_enum_non_zst_table() {
        if ty_is_definitely_non_zst(&ty) != expected {
            wrong.push(format!("{label}: expected {expected}"));
        }
    }
    assert!(wrong.is_empty(), "ty_is_definitely_non_zst disagrees on: {wrong:#?}");
}

/// `fn f(a: &[elem]) -> usize { let n = PtrMetadata(a); n }`.
fn zst_enum_slice_len_read(elem: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "test::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice { elem: Box::new(elem) }),
                    },
                    name: Some("a".into()),
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) },
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

/// The consumer, end to end: `conjoin_slice_len_bounds` over the overflow goal
/// of `a.len() * 2` must attach `a__slice_len <= isize::MAX` for a sized element
/// and must NOT attach it for `&[One]`. Before the fix the `&[One]` arm attached
/// it, which is what let the solver prove `len * 2` cannot overflow.
#[test]
fn zst_enum_slice_len_takes_no_isize_ceiling() {
    let ceiling_attached = |elem: Ty| -> bool {
        let func = zst_enum_slice_len_read(elem);
        let Some(len @ Formula::Var(..)) =
            crate::slice_len_formula(&func, &Operand::Copy(Place::local(1)))
        else {
            panic!("a slice place must mint a `__slice_len` var");
        };
        // `len * 2 > usize::MAX`, the overflow witness the mul row asks about.
        let goal = Formula::Gt(
            Box::new(Formula::Mul(Box::new(len.clone()), Box::new(Formula::Int(2)))),
            Box::new(Formula::Int(u64::MAX as i128)),
        );
        let ceiling = Formula::Le(Box::new(len), Box::new(Formula::Int(i64::MAX as i128)));
        match super::conjoin_slice_len_bounds(&func, goal.clone()) {
            Formula::And(conjuncts) => {
                assert_eq!(conjuncts.last(), Some(&goal), "the goal stays the last conjunct");
                conjuncts.contains(&ceiling)
            }
            other => {
                assert_eq!(other, goal, "no bound at all must leave the goal unchanged");
                false
            }
        }
    };
    assert!(ceiling_attached(Ty::Int { width: 8, signed: false }), "control: &[u8] is bounded");
    assert!(
        ceiling_attached(zst_enum_adt("Real", vec![("A", vec![]), ("B", vec![])])),
        "control: a two-variant fieldless enum is one byte"
    );
    assert!(
        !ceiling_attached(zst_enum_adt("One", vec![("A", vec![])])),
        "`&[One]` (enum One {{ A }}, a ZST) can be usize::MAX long"
    );
    assert!(
        !ceiling_attached(zst_enum_adt(
            "core::option::Option<core::convert::Infallible>",
            vec![("None", vec![]), ("Some", vec![zst_infallible()])],
        )),
        "`&[Option<Infallible>]` is a ZST slice"
    );
}

/// Build `fn f(p: <operand_ty>) { let _2 = PtrMetadata(Copy(_1)); }` so the
/// single statement exercises exactly the `collect_rvalue_unsupported`
/// PtrMetadata arm under test.
fn ptr_metadata_fn(operand_ty: Ty) -> VerifiableFunction {
    let metadata_ty = match &operand_ty {
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. }
            if matches!(inner.as_ref(), Ty::Slice { .. } | Ty::Str) =>
        {
            Ty::usize()
        }
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. }
            if !matches!(inner.as_ref(), Ty::Dynamic { .. } | Ty::Unsupported { .. }) =>
        {
            Ty::Unit
        }
        _ => Ty::usize(),
    };
    VerifiableFunction {
        name: "ptr_meta".to_string(),
        def_path: "test::ptr_meta".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // return
                LocalDecl { index: 1, ty: operand_ty, name: Some("p".into()) }, // operand
                LocalDecl { index: 2, ty: metadata_ty, name: Some("metadata".into()) },
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let unsupported = unsupported_mir_vcs(&func)
        .into_iter()
        .filter(
            |vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "TyKind::Alias"),
        )
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
fn str_metadata_uses_the_canonical_utf8_byte_length_for_direct_ref_and_raw_ptr() {
    let cases = [
        ("&str", Ty::Ref { mutable: false, inner: Box::new(Ty::Str) }),
        ("*const str", Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Str) }),
    ];

    for (label, ty) in cases {
        let func = ptr_metadata_fn(ty);
        assert_eq!(
            ptr_metadata_unsupported(&func),
            0,
            "PtrMetadata over {label} is its UTF-8 byte length"
        );
        let crate::PtrMetadataModel::Length(len) =
            crate::ptr_metadata_model(&func, &Operand::Copy(Place::local(1)))
        else {
            panic!("str-shaped metadata must have one canonical length term");
        };
        assert!(matches!(
            len,
            Formula::Var(name, Sort::Int) if name.ends_with("__slice_len")
        ));
    }
}

#[test]
fn sized_and_array_pointer_metadata_is_unit_not_length() {
    for ty in [
        Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
        Ty::Ref { mutable: false, inner: Box::new(Ty::Array { elem: Box::new(Ty::u8()), len: 7 }) },
        Ty::RawPtr {
            mutable: false,
            pointee: Box::new(Ty::Array { elem: Box::new(Ty::u8()), len: 7 }),
        },
    ] {
        let func = ptr_metadata_fn(ty);
        assert!(matches!(
            crate::ptr_metadata_model(&func, &Operand::Copy(Place::local(1))),
            crate::PtrMetadataModel::Unit
        ));
        assert_eq!(ptr_metadata_unsupported(&func), 0);
        assert!(validate_function(&func).is_ok());
    }
}

#[test]
fn dynamic_pointer_metadata_still_fails_closed() {
    let func = ptr_metadata_fn(Ty::RawPtr {
        mutable: false,
        pointee: Box::new(Ty::Dynamic {
            trait_name: "test::Trait".into(),
            principal_key: Some("test::Trait".into()),
        }),
    });
    assert_eq!(
        ptr_metadata_unsupported(&func),
        1,
        "PtrMetadata over a dyn pointer is unmodelable and must still emit \
         exactly one UnsupportedMir obligation"
    );
}

#[test]
fn ptr_metadata_rejects_nonpointer_wrong_destination_and_projection_carriers() {
    let nonpointer = ptr_metadata_fn(Ty::u32());
    assert!(matches!(
        validate_function(&nonpointer),
        Err(VcgenError::MalformedMir { detail, .. }) if detail.contains("pointer operand")
    ));

    let mut wrong_destination = ptr_metadata_fn(Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
    });
    wrong_destination.body.locals[2].ty = Ty::Unit;
    assert_ptr_metadata_malformed_fails_closed(&wrong_destination);

    let mut projected_destination =
        ptr_metadata_fn(Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) });
    let Statement::Assign { place, .. } = &mut projected_destination.body.blocks[0].stmts[0] else {
        unreachable!();
    };
    place.projections.push(Projection::Field(0));
    assert_ptr_metadata_malformed_fails_closed(&projected_destination);
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
fn try_into_unwrap_fn(start: u128, end: u128, arr_len: u64, result_ty: Ty) -> VerifiableFunction {
    let arr = Ty::Array { elem: Box::new(Ty::Int { width: 8, signed: false }), len: arr_len };
    let slice_ref =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    let range_ty = Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        variants: Vec::new().into(),
        name: "core::ops::Range".into(),
        fields: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    };
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
                        args: vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::ops::index::Index::index",
                        ),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::convert::TryInto::try_into",
                        ),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::result::Result::<T, E>::unwrap",
                        ),
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn result_array(n: u64) -> Ty {
    Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        variants: Vec::new().into(),
        name: "core::result::Result".into(),
        fields: vec![
            ("0".into(), Ty::Array { elem: Box::new(Ty::u8()), len: n }),
            ("1".into(), Ty::Unit),
        ]
        .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    }
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
                    ty: Ty::Adt {
                        arbitrary_precision: None,
                        validity_wrapper: None,
                        adt_kind: None,
                        layout: None,
                        variants: Vec::new().into(),
                        name: "core::result::Result".into(),
                        fields: vec![("0".into(), Ty::u64()), ("1".into(), Ty::Unit)].into(),
                        disc_index_safe: false,
                        faithful_enum_repr: None,
                        enum_layout: None,
                    },
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key("mycrate::fallible"),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::result::Result::<T, E>::unwrap",
                        ),
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
        inner: Box::new(Ty::Adt {
            arbitrary_precision: None,
            validity_wrapper: None,
            adt_kind: None,
            layout: None,
            variants: Vec::new().into(),
            name: "mycrate::MyWrap".into(),
            fields: vec![].into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        }),
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
    let rangefrom_ty = Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        variants: Vec::new().into(),
        name: "core::ops::RangeFrom".into(),
        fields: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    };
    let usize_ty = Ty::Int { width: 64, signed: false };
    let checked_sub_ty = Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        adt_kind: None,
        layout: None,
        variants: Vec::new().into(),
        name: "(usize, bool)".into(),
        fields: vec![("0".into(), usize_ty.clone()), ("1".into(), Ty::Bool)].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    };
    VerifiableFunction {
        name: "suffix".into(),
        def_path: "test::suffix".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None }, // _0 ret
                LocalDecl { index: 1, ty: slice_ref.clone(), name: Some("bytes".into()) }, // _1
                LocalDecl { index: 2, ty: usize_ty.clone(), name: Some("len".into()) }, // _2 len
                LocalDecl { index: 3, ty: arr, name: None },       // _3 [u8;N]
                LocalDecl { index: 4, ty: result_array(arr_len), name: None }, // _4 Result
                LocalDecl { index: 5, ty: slice_ref.clone(), name: None }, // _5 &[u8]
                LocalDecl { index: 6, ty: rangefrom_ty, name: None }, // _6 RangeFrom
                LocalDecl { index: 7, ty: usize_ty, name: None },  // _7 len-K value
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
                        args: vec![Operand::Copy(Place::local(1)), Operand::Move(Place::local(6))],
                        dest: Place::local(5),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::ops::index::Index::index",
                        ),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::convert::TryInto::try_into",
                        ),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::result::Result::<T, E>::unwrap",
                        ),
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            // `fn suffix(bytes: &[u8]) -> u64` — ONE parameter. `_2` (`len`) is a body
            // local (`let len = bytes.len()`), which is what `_2 = PtrMetadata(_1)`
            // lowers to; declaring it a parameter would make its ENTRY value a second
            // value of `_2` and withhold every fact keyed on the bare `len`.
            arg_count: 1,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
                    ty: Ty::Adt {
                        arbitrary_precision: None,
                        validity_wrapper: None,
                        adt_kind: None,
                        layout: None,
                        variants: Vec::new().into(),
                        name: "core::result::Result".into(),
                        fields: vec![("0".into(), Ty::u64()), ("1".into(), Ty::Unit)].into(),
                        disc_index_safe: false,
                        faithful_enum_repr: None,
                        enum_layout: None,
                    },
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key("mycrate::fallible"),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::result::Result::<T, E>::unwrap",
                        ),
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}
