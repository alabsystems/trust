//! TINV P1 on real MIR (2026-10-06): a call whose every argument hands the callee no
//! WRITE channel (`path_defs::arg_grants_no_write`) takes the dest-only arm, which
//! havocs its destination and (TINV-18 correction, coarse rule) every name of the
//! whole-function list except a protected, pointer-free `&mut` PARAMETER that never
//! leaves the body (`path_defs::escape_havoc`).
//!
//! The body is `fn f(r: &mut u32, s: &[u8], ..)` with `x` mutably borrowed, so the full
//! havoc list holds `r` and `x`; each test varies the call's arguments and asserts
//! whether the full list is applied (`r` havocked) or the dest-only arm is taken (`r`
//! kept; the `&mut`-borrowed stack local `x` is havocked by both).

use trust_types::{
    AdtKind, BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VariantDef, VerifiableBody, VerifiableFunction,
};

use super::terminator_def_names;

fn u8_ty() -> Ty {
    Ty::Int { width: 8, signed: false }
}

fn adt(name: &str, kind: AdtKind, fields: Vec<(String, Ty)>, variants: Vec<VariantDef>) -> Ty {
    Ty::Adt {
        adt_kind: Some(kind),
        layout: None,
        variants: variants.into(),
        name: name.into(),
        fields: fields.into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `Option<u8>` as the extractor spells it: an enum with a tag and a payload field.
fn option_u8() -> Ty {
    adt(
        "core::option::Option<u8>",
        AdtKind::Enum,
        vec![("__tag".into(), Ty::Int { width: 64, signed: true }), ("__v1_0".into(), u8_ty())],
        vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), u8_ty())],
            },
        ],
    )
}

fn shared(t: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(t) }
}

/// Locals: `_0` ret, `_1 r: &mut u32` (param), `_2 s: &[u8]` (param), `_3` a `&mut x`
/// temp, `_4 x: u32`, then `_5` = `extra`.
fn call_func(extra: Ty, args: Vec<Operand>, is_foreign: bool) -> VerifiableFunction {
    let u32_ty = Ty::Int { width: 32, signed: false };
    let locals = vec![
        (Ty::Unit, Some("ret")),
        (Ty::Ref { mutable: true, inner: Box::new(u32_ty.clone()) }, Some("r")),
        (shared(Ty::Slice { elem: Box::new(u8_ty()) }), Some("s")),
        (Ty::Ref { mutable: true, inner: Box::new(u32_ty.clone()) }, None),
        (u32_ty, Some("x")),
        (extra, None),
    ];
    VerifiableFunction {
        name: "f".into(),
        def_path: "test::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, (ty, name))| LocalDecl { index, ty, name: name.map(Into::into) })
                .collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Ref { mutable: true, place: Place::local(4) },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "test::callee".into(),
                    args,
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key("test::callee"),
                    is_foreign,
                },
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
    }
}

fn havocs_aliases(func: &VerifiableFunction) -> bool {
    let names = terminator_def_names(func, &func.body.blocks[0]);
    names.iter().any(|n| n == "r") && names.iter().any(|n| n == "x")
}

/// The dest-only arm: the destination is written, the protected parameter `r` keeps
/// its facts, and the `&mut`-borrowed stack local `x` is still havocked.
fn takes_the_dest_only_arm(func: &VerifiableFunction) -> bool {
    let names = terminator_def_names(func, &func.body.blocks[0]);
    names.iter().any(|n| n == "ret")
        && names.iter().any(|n| n == "x")
        && !names.iter().any(|n| n == "r")
}

#[test]
fn a_shared_slice_argument_havocs_only_the_destination() {
    // `<[u8]>::len(s)`: the callee can read `*s` and write nothing.
    let func = call_func(Ty::Unit, vec![Operand::Copy(Place::local(2))], false);
    assert!(
        takes_the_dest_only_arm(&func),
        "{:?}",
        terminator_def_names(&func, &func.body.blocks[0])
    );
}

#[test]
fn a_shared_reference_to_a_shared_slice_havocs_only_the_destination() {
    // `PartialEq::eq(&s, ..)`: `_5 = &s`, a `&&[u8]`.
    let mut func = call_func(
        shared(shared(Ty::Slice { elem: Box::new(u8_ty()) })),
        vec![Operand::Move(Place::local(5))],
        false,
    );
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::Ref { mutable: false, place: Place::local(2) },
        span: SourceSpan::default(),
    });
    assert!(takes_the_dest_only_arm(&func));
}

#[test]
fn a_by_value_pure_enum_havocs_only_the_destination() {
    // `<Option<u8> as Try>::branch(move o)`.
    let func = call_func(option_u8(), vec![Operand::Move(Place::local(5))], false);
    assert!(takes_the_dest_only_arm(&func));
}

#[test]
fn a_mutable_reference_argument_keeps_the_full_havoc() {
    let func = call_func(Ty::Unit, vec![Operand::Copy(Place::local(1))], false);
    assert!(havocs_aliases(&func));
    // `&mut [u8]` too.
    let func = call_func(
        Ty::Ref { mutable: true, inner: Box::new(Ty::Slice { elem: Box::new(u8_ty()) }) },
        vec![Operand::Move(Place::local(5))],
        false,
    );
    assert!(havocs_aliases(&func));
}

#[test]
fn a_shared_reference_to_a_mutable_reference_keeps_the_full_havoc() {
    // `& &mut u32`: no write through it in safe code, but the pointee is not
    // pointer-free `Freeze` data, so it is not admitted.
    let func = call_func(
        shared(Ty::Ref { mutable: true, inner: Box::new(Ty::Int { width: 32, signed: false }) }),
        vec![Operand::Move(Place::local(5))],
        false,
    );
    assert!(havocs_aliases(&func));
}

#[test]
fn a_shared_reference_to_interior_mutability_keeps_the_full_havoc() {
    let cell = adt(
        "core::cell::Cell<u32>",
        AdtKind::Struct,
        vec![("value".into(), Ty::Int { width: 32, signed: false })],
        vec![],
    );
    let func = call_func(shared(cell), vec![Operand::Move(Place::local(5))], false);
    assert!(havocs_aliases(&func));
}

#[test]
fn a_by_value_adt_carrying_a_pointer_keeps_the_full_havoc() {
    let carrier = adt(
        "test::Carrier",
        AdtKind::Struct,
        vec![(
            "p".into(),
            Ty::RawPtr { mutable: true, pointee: Box::new(Ty::Int { width: 32, signed: false }) },
        )],
        vec![],
    );
    let func = call_func(carrier, vec![Operand::Move(Place::local(5))], false);
    assert!(havocs_aliases(&func));
    // An unstamped ADT is refused even when its rendered fields are pure.
    let mut unstamped = option_u8();
    if let Ty::Adt { adt_kind, .. } = &mut unstamped {
        *adt_kind = None;
    }
    let func = call_func(unstamped, vec![Operand::Move(Place::local(5))], false);
    assert!(havocs_aliases(&func));
}

#[test]
fn a_shared_slice_into_a_foreign_callee_keeps_the_full_havoc() {
    // Code across an FFI boundary is outside the aliasing model the shared-reference
    // rule rests on (the TRUST-10 / 13b fence).
    let func = call_func(Ty::Unit, vec![Operand::Copy(Place::local(2))], true);
    assert!(havocs_aliases(&func));
}

#[test]
fn a_pointer_laundering_site_keeps_the_full_havoc_for_a_shared_slice() {
    let mut func = call_func(Ty::Unit, vec![Operand::Copy(Place::local(2))], false);
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::AddressOf(true, Place::local(4)),
        span: SourceSpan::default(),
    });
    assert!(havocs_aliases(&func));
}

#[test]
fn a_shared_reference_of_unknown_provenance_keeps_the_full_havoc() {
    // `_5: &[u8]` with no definition the analysis can read (a call destination in real
    // MIR): it may be a reborrow of memory under a `&mut`, which this rule leaves to
    // the TRUST-10 / 13b refinements.
    let func = call_func(
        shared(Ty::Slice { elem: Box::new(u8_ty()) }),
        vec![Operand::Move(Place::local(5))],
        false,
    );
    assert!(havocs_aliases(&func));
}

#[test]
fn a_reborrow_through_a_mutable_reference_is_left_to_the_older_refinements() {
    // `_5 = &(*r)` with `r: &mut u32`: not decided by this rule. 13b may narrow `r`
    // itself, but the `&mut x` local must stay havoced.
    let mut func = call_func(
        shared(Ty::Int { width: 32, signed: false }),
        vec![Operand::Move(Place::local(5))],
        false,
    );
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::Ref {
            mutable: false,
            place: Place { local: 1, projections: vec![trust_types::Projection::Deref] },
        },
        span: SourceSpan::default(),
    });
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert!(names.iter().any(|n| n == "x"), "{names:?}");
}

#[test]
fn a_field_less_struct_by_value_keeps_the_full_havoc() {
    // The extractor recorded no fields: nothing proves it holds no pointer.
    let func = call_func(
        adt("p::Z", AdtKind::Struct, vec![], vec![]),
        vec![Operand::Move(Place::local(5))],
        false,
    );
    assert!(havocs_aliases(&func));
}
