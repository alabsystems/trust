//! TINV step 4b: the place-write classifier, one row per channel and rule.

use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, PlaceWriteChannel, Projection,
    Rvalue, SourceSpan, Statement, Terminator, Ty, UnOp, UnwindEdge, VerifiableBody,
    VerifiableFunction,
};

use super::*;

fn adt(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: name.into(),
        fields: fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect::<Vec<_>>().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

/// `c::S { a: u64, n: u64 }`.
fn s_ty() -> Ty {
    adt("c::S", vec![("a", u64_ty()), ("n", u64_ty())])
}

/// A decoy with the same field indices.
fn t_ty() -> Ty {
    adt("c::T", vec![("a", u64_ty()), ("n", u64_ty())])
}

fn mut_ref(t: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(t) }
}

fn raw(t: Ty) -> Ty {
    Ty::RawPtr { mutable: true, pointee: Box::new(t) }
}

fn func(locals: Vec<Ty>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "c::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: Ty::Unit,
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks,
            arg_count: 1,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn one_block(stmts: Vec<Statement>, terminator: Terminator) -> Vec<BasicBlock> {
    vec![BasicBlock { id: BlockId(0), stmts, terminator }]
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn konst() -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Int(0)))
}

fn place(local: usize, projections: Vec<Projection>) -> Place {
    Place { local, projections }
}

fn fields_of(findings: &[WriteFinding]) -> Vec<(String, usize, bool, Via)> {
    findings
        .iter()
        .filter_map(|f| match f {
            WriteFinding::Field { adt, field, element_only, via, .. } => {
                Some((adt.clone(), *field, *element_only, via.clone()))
            }
            _ => None,
        })
        .collect()
}

#[test]
fn a_store_through_mut_self_hits_exactly_the_written_field() {
    // _1: &mut S; (*_1).1 = 0.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty())],
        one_block(
            vec![assign(place(1, vec![Projection::Deref, Projection::Field(1)]), konst())],
            Terminator::Return,
        ),
    );
    let findings = classify_writes(&f);
    assert_eq!(fields_of(&findings), vec![("c::S".into(), 1, false, Via::ThroughRef)]);
    assert!(writes_fields_of(&f, "c::S", &[1]));
    assert!(!writes_fields_of(&f, "c::S", &[0]));
    // A same-index decoy ADT gets no hit.
    assert!(!writes_fields_of(&f, "c::T", &[1]));
    assert_eq!(tinv_refusal(&f, &findings, "c::S"), None);
}

#[test]
fn findings_name_the_place_the_field_hangs_off() {
    // _1: &mut S; (*_1).1 = 0 -> owner `*_1`.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty())],
        one_block(
            vec![assign(place(1, vec![Projection::Deref, Projection::Field(1)]), konst())],
            Terminator::Return,
        ),
    );
    let owners: Vec<Place> = classify_writes(&f)
        .into_iter()
        .filter_map(|w| match w {
            WriteFinding::Field { owner, .. } => Some(owner),
            _ => None,
        })
        .collect();
    assert_eq!(owners, vec![place(1, vec![Projection::Deref])]);
}

#[test]
fn a_whole_value_store_names_the_adt() {
    // _1: &mut S; _2: S; (*_1) = move _2.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty()), s_ty()],
        one_block(
            vec![assign(
                place(1, vec![Projection::Deref]),
                Rvalue::Use(Operand::Move(Place::local(2))),
            )],
            Terminator::Return,
        ),
    );
    assert!(classify_writes(&f).iter().any(|w| matches!(w,
        WriteFinding::WholeValue { adt, channel: PlaceWriteChannel::Store, .. } if adt == "c::S")));
}

#[test]
fn an_indexed_write_is_element_only() {
    // S2 { arr: [u64; 4] }; _1: &mut S2; _3: usize; (*_1).0[_3] = 0.
    let s2 = adt("c::S2", vec![("arr", Ty::Array { elem: Box::new(u64_ty()), len: 4 })]);
    let f = func(
        vec![Ty::Unit, mut_ref(s2), Ty::Unit, u64_ty()],
        one_block(
            vec![assign(
                place(1, vec![Projection::Deref, Projection::Field(0), Projection::Index(3)]),
                konst(),
            )],
            Terminator::Return,
        ),
    );
    assert_eq!(fields_of(&classify_writes(&f)), vec![("c::S2".into(), 0, true, Via::ThroughRef)]);
    // The backing lane ignores element-only writes.
    assert!(!writes_fields_of(&f, "c::S2", &[0]));
}

#[test]
fn a_write_through_a_raw_pointer_refuses_the_pointee_type() {
    // _1: *mut S; (*_1).1 = 0.
    let f = func(
        vec![Ty::Unit, raw(s_ty())],
        one_block(
            vec![assign(place(1, vec![Projection::Deref, Projection::Field(1)]), konst())],
            Terminator::Return,
        ),
    );
    let findings = classify_writes(&f);
    assert!(matches!(
        fields_of(&findings).as_slice(),
        [(adt, 1, false, Via::ThroughRaw { .. })] if adt == "c::S"
    ));
    assert!(tinv_refusal(&f, &findings, "c::S").is_some());
    // An unrelated candidate is not refused by it.
    assert_eq!(tinv_refusal(&f, &findings, "c::T"), None);
}

#[test]
fn a_box_temp_write_keeps_the_owners_hit() {
    // Buf { len: u64 }; S3 { b: Box<Buf> }; _1: &mut S3; _2: *const Buf;
    // _2 = Cast(Copy((*_1).0.0.0), *const Buf); (*_2).0 = 0.
    let buf = adt("c::Buf", vec![("len", u64_ty())]);
    let nonnull = adt("core::ptr::non_null::NonNull", vec![("pointer", raw(buf.clone()))]);
    let unique = adt("core::ptr::unique::Unique", vec![("pointer", nonnull)]);
    let boxed = adt("alloc::boxed::Box", vec![("0", unique)]);
    let s3 = adt("c::S3", vec![("b", boxed)]);
    let src = place(
        1,
        vec![Projection::Deref, Projection::Field(0), Projection::Field(0), Projection::Field(0)],
    );
    let f = func(
        vec![Ty::Unit, mut_ref(s3), raw(buf.clone())],
        one_block(
            vec![
                assign(Place::local(2), Rvalue::Cast(Operand::Copy(src), raw(buf))),
                assign(place(2, vec![Projection::Deref, Projection::Field(0)]), konst()),
            ],
            Terminator::Return,
        ),
    );
    let hits = fields_of(&classify_writes(&f));
    assert!(hits.iter().any(|(a, fld, _, _)| a == "c::S3" && *fld == 0), "{hits:?}");
    assert!(
        hits.iter().any(|(a, fld, _, via)| a == "c::Buf"
            && *fld == 0
            && !matches!(via, Via::ThroughRaw { .. })),
        "{hits:?}"
    );
    // The same shape from a non-Box source is a raw-pointer write.
    let plain = adt("c::NotBox", vec![("0", adt("c::U", vec![("p", raw(t_ty()))]))]);
    let g = func(
        vec![Ty::Unit, mut_ref(adt("c::S4", vec![("b", plain)])), raw(t_ty())],
        one_block(
            vec![
                assign(
                    Place::local(2),
                    Rvalue::Cast(
                        Operand::Copy(place(
                            1,
                            vec![
                                Projection::Deref,
                                Projection::Field(0),
                                Projection::Field(0),
                                Projection::Field(0),
                            ],
                        )),
                        raw(t_ty()),
                    ),
                ),
                assign(place(2, vec![Projection::Deref, Projection::Field(0)]), konst()),
            ],
            Terminator::Return,
        ),
    );
    assert!(
        fields_of(&classify_writes(&g))
            .iter()
            .any(|(a, _, _, via)| a == "c::T" && matches!(via, Via::ThroughRaw { .. }))
    );
}

#[test]
fn a_fake_metadata_borrow_is_not_a_write_but_a_second_use_makes_it_one() {
    // _2 = &raw const (*_1).1; _3 = PtrMetadata(copy _2).
    let stmts = |extra: bool| {
        let mut v = vec![
            assign(
                Place::local(2),
                Rvalue::AddressOf(false, place(1, vec![Projection::Deref, Projection::Field(1)])),
            ),
            assign(
                Place::local(3),
                Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(2))),
            ),
        ];
        if extra {
            v.push(assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(2)))));
        }
        v
    };
    let locals = vec![Ty::Unit, mut_ref(s_ty()), raw(u64_ty()), u64_ty(), raw(u64_ty())];
    let exempt = func(locals.clone(), one_block(stmts(false), Terminator::Return));
    assert!(!writes_fields_of(&exempt, "c::S", &[1]));
    let used = func(locals, one_block(stmts(true), Terminator::Return));
    assert!(classify_writes(&used).iter().any(|w| matches!(w,
        WriteFinding::Field { adt, field: 1, channel: PlaceWriteChannel::RawBorrow { mutable: false }, .. }
            if adt == "c::S")));
}

/// INT-RAWCONST-HAVOC-1 (2026-10-06): `write_capable_borrow` is the one borrow test
/// behind vcgen's general havoc list, its def-scan siblings, the backing index scan and
/// trust-clean's alias gates. Every raw borrow counts, of either mutability, except the
/// extractor's fake-metadata `&raw const` (one definition, one `PtrMetadata` read).
#[test]
fn write_capable_borrow_counts_every_raw_borrow_but_the_fake_metadata_one() {
    let field = place(1, vec![Projection::Deref, Projection::Field(1)]);
    let locals = vec![Ty::Unit, mut_ref(s_ty()), raw(u64_ty()), u64_ty(), raw(u64_ty())];
    let lend = |rvalue: Rvalue| assign(Place::local(2), rvalue);
    let metadata = || {
        assign(Place::local(3), Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(2))))
    };
    let copy_out = || assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(2))));
    let rows: Vec<(&str, Vec<Statement>, bool)> = vec![
        ("&mut", vec![lend(Rvalue::Ref { mutable: true, place: field.clone() })], true),
        ("& (shared)", vec![lend(Rvalue::Ref { mutable: false, place: field.clone() })], false),
        ("&raw mut", vec![lend(Rvalue::AddressOf(true, field.clone()))], true),
        ("&raw const, unused", vec![lend(Rvalue::AddressOf(false, field.clone()))], true),
        (
            "&raw const, read by PtrMetadata and copied out",
            vec![lend(Rvalue::AddressOf(false, field.clone())), metadata(), copy_out()],
            true,
        ),
        (
            "&raw const, read only by PtrMetadata (fake metadata)",
            vec![lend(Rvalue::AddressOf(false, field.clone())), metadata()],
            false,
        ),
        (
            "&raw mut, read only by PtrMetadata",
            vec![lend(Rvalue::AddressOf(true, field.clone())), metadata()],
            true,
        ),
    ];
    for (label, stmts, expected) in rows {
        let f = func(locals.clone(), one_block(stmts, Terminator::Return));
        let first = &f.body.blocks[0].stmts[0];
        assert_eq!(
            write_capable_borrow(&f.body, first, |p| *p == field).is_some(),
            expected,
            "{label}"
        );
        // `wanted` gates the answer.
        assert!(write_capable_borrow(&f.body, first, |_| false).is_none(), "{label}: wanted");
        if expected {
            assert_eq!(write_capable_borrow(&f.body, first, |_| true), Some(&field), "{label}");
        }
    }
    // A statement that borrows nothing.
    let f = func(locals, one_block(vec![assign(Place::local(3), konst())], Terminator::Return));
    assert!(write_capable_borrow(&f.body, &f.body.blocks[0].stmts[0], |_| true).is_none());

    // Through a SHARED reference `_1: &S`, a `&raw const` grants what `&(*_1).1` grants
    // and does not count; a `&raw mut` there is not well-typed Rust but still counts, and
    // a `&raw const` of the reference local's OWN storage counts.
    let shared_locals = vec![
        Ty::Unit,
        Ty::Ref { mutable: false, inner: Box::new(s_ty()) },
        raw(u64_ty()),
        u64_ty(),
        raw(u64_ty()),
    ];
    let shared_rows: Vec<(&str, Rvalue, bool)> = vec![
        ("&raw const (*shared).1", Rvalue::AddressOf(false, field.clone()), false),
        (
            "&raw const (*shared)",
            Rvalue::AddressOf(false, place(1, vec![Projection::Deref])),
            false,
        ),
        ("&raw mut (*shared).1", Rvalue::AddressOf(true, field.clone()), true),
        ("&raw const shared (its own storage)", Rvalue::AddressOf(false, Place::local(1)), true),
    ];
    for (label, rvalue, expected) in shared_rows {
        let f = func(
            shared_locals.clone(),
            one_block(vec![lend(rvalue), copy_out()], Terminator::Return),
        );
        let first = &f.body.blocks[0].stmts[0];
        assert_eq!(write_capable_borrow(&f.body, first, |_| true).is_some(), expected, "{label}");
    }
}

#[test]
fn unlocatable_writes_refuse_every_candidate_except_an_abort() {
    let intrinsic = func(
        vec![Ty::Unit],
        one_block(
            vec![Statement::Intrinsic { name: "assume".into(), args: vec![] }],
            Terminator::Return,
        ),
    );
    let findings = classify_writes(&intrinsic);
    assert!(findings.iter().any(|w| matches!(w, WriteFinding::Unlocatable { .. })));
    assert!(tinv_refusal(&intrinsic, &findings, "c::S").is_some());
    let opaque = |kind: &str| {
        func(
            vec![Ty::Unit],
            one_block(
                vec![],
                Terminator::Opaque {
                    kind: kind.into(),
                    targets: vec![],
                    span: SourceSpan::default(),
                },
            ),
        )
    };
    assert!(
        classify_writes(&opaque("InlineAsm"))
            .iter()
            .any(|w| matches!(w, WriteFinding::Unlocatable { .. }))
    );
    // convert.rs spells an abort `UnwindTerminate(..)`; it writes nothing.
    assert!(classify_writes(&opaque("UnwindTerminate(InCleanup)")).is_empty());
}

#[test]
fn an_unsupported_rvalue_stores_its_destination_and_reports_its_operands() {
    // _2 = Unsupported(copy (*_1)); the operand's type is S.
    let f = func(
        vec![Ty::Unit, mut_ref(s_ty()), u64_ty()],
        one_block(
            vec![assign(
                Place::local(2),
                Rvalue::Unsupported {
                    kind: "PointerCoercion".into(),
                    detail: String::new(),
                    operands: vec![Operand::Copy(place(1, vec![Projection::Deref]))],
                },
            )],
            Terminator::Return,
        ),
    );
    let findings = classify_writes(&f);
    assert!(findings.iter().any(|w| matches!(w, WriteFinding::UnsupportedOperand { .. })));
    assert!(tinv_refusal(&f, &findings, "c::S").is_some());
    assert_eq!(tinv_refusal(&f, &findings, "c::T"), None);
}

#[test]
fn call_arguments_are_judged_by_type_reach() {
    let ctx = adt("c::Ctx", vec![("s", mut_ref(s_ty()))]);
    let defs = Default::default();
    assert_eq!(type_reaches(&mut_ref(s_ty()), "c::S", &defs), Reach::Yes);
    assert_eq!(type_reaches(&ctx, "c::S", &defs), Reach::Yes);
    assert_eq!(
        type_reaches(&Ty::Array { elem: Box::new(s_ty()), len: 2 }, "c::S", &defs),
        Reach::Yes
    );
    assert_eq!(type_reaches(&u64_ty(), "c::S", &defs), Reach::No);
    assert_eq!(type_reaches(&t_ty(), "c::S", &defs), Reach::No);
    let coroutine = Ty::Coroutine { name: "g".into(), upvars: vec![] };
    assert_eq!(type_reaches(&coroutine, "c::S", &defs), Reach::Unknown);
    // An argument of unknown reach refuses; a known one is a CallArg for step 7.
    let call = |arg_ty: Ty| {
        func(
            vec![Ty::Unit, arg_ty, Ty::Unit],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "g".into(),
                        args: vec![Operand::Move(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: UnwindEdge::Continue,
                        callee_identity: None,
                        callee_key: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        )
    };
    let unknown = call(coroutine);
    let findings = classify_writes(&unknown);
    assert!(tinv_refusal(&unknown, &findings, "c::S").is_some());
    let known = call(ctx);
    let findings = classify_writes(&known);
    assert!(findings.iter().any(|w| matches!(w, WriteFinding::CallArg { arg_idx: 0, .. })));
    assert_eq!(tinv_refusal(&known, &findings, "c::S"), None);
}

// --- Recursive datatype markers: `type_reaches` is a least fixpoint over marker names.

fn marker(name: &str) -> Ty {
    Ty::Datatype { name: name.into(), variants: vec![] }
}

fn seq(elem: Ty) -> Ty {
    Ty::Seq { elem: Box::new(elem), drop_auth: None }
}

fn defs_of(tys: Vec<Ty>) -> trust_types::DatatypeDefs {
    let mut defs = trust_types::DatatypeDefs::new();
    for t in tys {
        assert!(trust_types::insert_datatype_def(&mut defs, t));
    }
    defs
}

/// `enum Json { Null, Num(u64), Arr(Vec<Json>), Obj(Vec<(String, Json)>) }`, flattened as
/// the extractor writes an enum (`__v{v}_{f}` fields), with `extra` fields appended.
fn json_def(name: &str, extra: Vec<(&str, Ty)>) -> Ty {
    let mut fields = vec![
        ("__tag", u64_ty()),
        ("__v1_0", u64_ty()),
        ("__v2_0", seq(marker(name))),
        ("__v3_0", seq(Ty::Tuple(vec![Ty::Str, marker(name)]))),
    ];
    fields.extend(extra);
    adt(name, fields)
}

#[test]
fn recursive_marker_without_s_answers_no() {
    // Before the fixpoint this burnt the 4096 fuel and answered Unknown for ANY S.
    let defs = defs_of(vec![json_def("w::Json", vec![])]);
    let arg = Ty::Ref {
        mutable: false,
        inner: Box::new(seq(Ty::Tuple(vec![Ty::Str, marker("w::Json")]))),
    };
    assert_eq!(type_reaches(&arg, "w::Parser", &defs), Reach::No);
    assert_eq!(type_reaches(&marker("w::Json"), "w::Parser", &defs), Reach::No);
    // The marker itself IS the named type.
    assert_eq!(type_reaches(&arg, "w::Json", &defs), Reach::Yes);
}

#[test]
fn recursive_marker_reaching_s_answers_yes_on_either_side_of_the_back_edge() {
    // `enum T { Leaf(S), Node(Vec<T>) }` and `enum T { Node(Vec<T>), Leaf(S) }`.
    let before =
        adt("w::T", vec![("__tag", u64_ty()), ("__v0_0", s_ty()), ("__v1_0", seq(marker("w::T")))]);
    let after =
        adt("w::T", vec![("__tag", u64_ty()), ("__v0_0", seq(marker("w::T"))), ("__v1_0", s_ty())]);
    for def in [before, after] {
        let defs = defs_of(vec![def]);
        assert_eq!(type_reaches(&seq(marker("w::T")), "c::S", &defs), Reach::Yes);
        assert_eq!(type_reaches(&marker("w::T"), "c::S", &defs), Reach::Yes);
        // Through a mutable reference too: `&mut S` inside the recursive type.
        assert_eq!(type_reaches(&marker("w::T"), "c::T", &defs), Reach::No);
    }
    let via_ref =
        json_def("w::Json", vec![("__v4_0", mut_ref(adt("w::Parser", vec![("pos", u64_ty())])))]);
    let defs = defs_of(vec![via_ref]);
    assert_eq!(type_reaches(&seq(marker("w::Json")), "w::Parser", &defs), Reach::Yes);
}

#[test]
fn recursive_marker_with_an_opaque_field_stays_unknown() {
    let dyn_ty = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Dynamic { trait_name: "t::Tr".into(), principal_key: None }),
    };
    let unsupported = Ty::Unsupported { kind: "Param".into(), detail: "T".into() };
    for opaque in [dyn_ty, unsupported] {
        // The opaque field after the back edge, and before it.
        let late = json_def("w::Json", vec![("__v4_0", opaque.clone())]);
        let early = adt(
            "w::Json",
            vec![("__tag", u64_ty()), ("__v0_0", opaque), ("__v1_0", seq(marker("w::Json")))],
        );
        for def in [late, early] {
            let defs = defs_of(vec![def]);
            assert_eq!(type_reaches(&seq(marker("w::Json")), "w::Parser", &defs), Reach::Unknown);
            assert_eq!(type_reaches(&marker("w::Json"), "w::Parser", &defs), Reach::Unknown);
        }
    }
}

#[test]
fn missing_marker_stays_unknown() {
    let defs = defs_of(vec![json_def("w::Json", vec![])]);
    assert_eq!(type_reaches(&marker("w::Other"), "w::Parser", &defs), Reach::Unknown);
    // A recursive def that mentions an undefined marker stays Unknown as well.
    let defs = defs_of(vec![json_def("w::Json", vec![("__v4_0", marker("w::Gone"))])]);
    assert_eq!(type_reaches(&marker("w::Json"), "w::Parser", &defs), Reach::Unknown);
    // A generics-erased spelling is a different key and does not resolve.
    let defs = defs_of(vec![json_def("w::Big<u8>", vec![])]);
    assert_eq!(type_reaches(&marker("w::Big<i32>"), "w::Parser", &defs), Reach::Unknown);
    assert_eq!(type_reaches(&marker("w::Big<u8>"), "w::Parser", &defs), Reach::No);
}

#[test]
fn mutually_recursive_markers() {
    let a = adt("w::A", vec![("bs", seq(marker("w::B")))]);
    let b = adt("w::B", vec![("as_", seq(marker("w::A"))), ("n", u64_ty())]);
    let defs = defs_of(vec![a, b]);
    assert_eq!(type_reaches(&marker("w::A"), "c::S", &defs), Reach::No);
    assert_eq!(type_reaches(&marker("w::B"), "c::S", &defs), Reach::No);
    let a = adt("w::A", vec![("bs", seq(marker("w::B")))]);
    let b = adt("w::B", vec![("as_", seq(marker("w::A"))), ("s", s_ty())]);
    let defs = defs_of(vec![a, b]);
    assert_eq!(type_reaches(&marker("w::A"), "c::S", &defs), Reach::Yes);
    let a = adt("w::A", vec![("bs", seq(marker("w::B")))]);
    let b = adt(
        "w::B",
        vec![
            ("as_", seq(marker("w::A"))),
            ("d", Ty::Unsupported { kind: "Param".into(), detail: "T".into() }),
        ],
    );
    let defs = defs_of(vec![a, b]);
    assert_eq!(type_reaches(&marker("w::A"), "c::S", &defs), Reach::Unknown);
}

/// Real MIR (ALab blocker (a)). `tests/fixtures/tinv_recursive_reach_fx.json` is the
/// `tinv-inventory.json` that the stage 1 of `tinv/alab-blockers` dumped for
/// `tests/fixtures/tinv_recursive_reach_fx.rs`, verbatim:
///
/// ```text
/// TRUST_TINV_NOTES=1 trustc --edition 2021 --crate-type lib --crate-name tinvrec \
///   -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-tinv -Ztrust-dump=mir:<dir> \
///   tinv_recursive_reach_fx.rs
/// ```
///
/// The derived `<Json as Clone>::clone` passes `&Vec<Json>` / `&Vec<(String, Json)>` to
/// `Vec::clone`; their extracted types mention the bare `tinvrec::Json` marker, whose table
/// definition mentions it again. Every such argument must reach `tinvrec::P` as `No` (it
/// was `Unknown`, out of fuel, which withheld `P` at the mint) and `tinvrec::Json` as `Yes`.
#[test]
fn realmir_recursive_json_clone_arguments_do_not_reach_the_parser() {
    #[derive(serde::Deserialize)]
    struct Row {
        func: VerifiableFunction,
    }
    let rows: Vec<Row> =
        serde_json::from_str(include_str!("../tests/fixtures/tinv_recursive_reach_fx.json"))
            .expect("the inventory fixture deserializes");
    let clone = rows
        .iter()
        .map(|r| &r.func)
        .find(|f| f.def_path == "<tinvrec::Json as core::clone::Clone>::clone")
        .expect("the derived clone is inventoried");
    let defs = &clone.body.datatype_defs;
    assert!(defs.contains_key("tinvrec::Json"), "the recursive marker has a table entry");
    let findings = classify_writes(clone);
    let mut recursive_args = 0;
    for finding in &findings {
        if let WriteFinding::CallArg { ty, site, .. } = finding
            && format!("{ty:?}").contains("tinvrec::Json")
        {
            recursive_args += 1;
            assert_eq!(type_reaches(ty, "tinvrec::P", defs), Reach::No, "at {site}");
            assert_eq!(type_reaches(ty, "tinvrec::Json", defs), Reach::Yes, "at {site}");
        }
    }
    assert!(recursive_args >= 2, "the Arr and Obj arms each pass a recursive argument");
    assert_eq!(tinv_refusal(clone, &findings, "tinvrec::P"), None);
    // Every inventoried body: no write refusal for `P` comes from the recursion.
    for r in &rows {
        let findings = classify_writes(&r.func);
        if let Some(why) = tinv_refusal(&r.func, &findings, "tinvrec::P") {
            assert!(!why.contains("unknown reach"), "{}: {why}", r.func.def_path);
        }
    }
}

// --- Decision TINV-33: the census's `dyn` / type-parameter evidence.

fn dyn_ref() -> Ty {
    Ty::Ref {
        mutable: true,
        inner: Box::new(Ty::Dynamic { trait_name: "core::fmt::Write".into(), principal_key: None }),
    }
}

fn param_ty() -> Ty {
    Ty::Unsupported { kind: "TyKind::Param".into(), detail: "I".into() }
}

#[test]
fn opaque_evidence_clears_only_what_it_names() {
    let defs = Default::default();
    // `&mut Formatter` holds `&mut dyn Write`.
    let formatter = adt("core::fmt::Formatter", vec![("flags", u64_ty()), ("buf", dyn_ref())]);
    let none = OpaqueReach::default();
    let dyn_only = OpaqueReach { dyn_cannot_reach: true, param_cannot_reach: false };
    let both = OpaqueReach { dyn_cannot_reach: true, param_cannot_reach: true };
    // No evidence: unchanged (`type_reaches` is the no-evidence walk).
    assert_eq!(type_reaches_with(&mut_ref(formatter.clone()), "c::S", &defs, none), Reach::Unknown);
    assert_eq!(type_reaches(&mut_ref(formatter.clone()), "c::S", &defs), Reach::Unknown);
    assert_eq!(type_reaches_with(&param_ty(), "c::S", &defs, none), Reach::Unknown);
    // The `dyn` evidence clears a trait object, never a parameter.
    assert_eq!(type_reaches_with(&mut_ref(formatter.clone()), "c::S", &defs, dyn_only), Reach::No);
    assert_eq!(type_reaches_with(&param_ty(), "c::S", &defs, dyn_only), Reach::Unknown);
    assert_eq!(type_reaches_with(&param_ty(), "c::S", &defs, both), Reach::No);
    // Neither clears any other opaque shape, nor hides an S that is really there.
    let alias =
        Ty::Unsupported { kind: "TyKind::Alias".into(), detail: "<I as Iterator>::Item".into() };
    let coroutine = Ty::Coroutine { name: "g".into(), upvars: vec![] };
    for t in [alias, coroutine, marker("c::Gone")] {
        assert_eq!(type_reaches_with(&t, "c::S", &defs, both), Reach::Unknown, "{t:?}");
    }
    let s_beside_dyn = Ty::Tuple(vec![dyn_ref(), mut_ref(s_ty())]);
    assert_eq!(type_reaches_with(&s_beside_dyn, "c::S", &defs, both), Reach::Yes);
    // Inside a recursive marker too.
    let defs = defs_of(vec![json_def("w::Json", vec![("__v4_0", dyn_ref())])]);
    assert_eq!(type_reaches_with(&marker("w::Json"), "w::Parser", &defs, none), Reach::Unknown);
    assert_eq!(type_reaches_with(&marker("w::Json"), "w::Parser", &defs, dyn_only), Reach::No);
}

#[test]
fn opaque_evidence_lifts_the_call_argument_refusal() {
    let formatter = adt("core::fmt::Formatter", vec![("flags", u64_ty()), ("buf", dyn_ref())]);
    let f = func(
        vec![Ty::Unit, mut_ref(formatter), Ty::Unit],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "core::fmt::Formatter::write_str".into(),
                    args: vec![Operand::Move(Place::local(1))],
                    dest: Place::local(2),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: UnwindEdge::Continue,
                    callee_identity: None,
                    callee_key: None,
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
    );
    let findings = classify_writes(&f);
    let why = tinv_refusal(&f, &findings, "c::S").expect("no evidence: refused");
    assert!(why.contains("unknown reach at bb0[0] in `"), "{why}");
    let dyn_only = OpaqueReach { dyn_cannot_reach: true, param_cannot_reach: false };
    assert_eq!(tinv_refusal_with(&f, &findings, "c::S", dyn_only), None);
}
