//! Resolution-layer pins for the ENUM VARIANT PAYLOAD range fact.
//!
//! The verdict matrix lives in `tests/enum_payload_range.rs` on real extracted
//! MIR. These tests cover the two things a verdict cannot see:
//!
//!   * the resolved `(width, signed)` for a payload whose VERDICT is carried by
//!     something else (the nested row), and
//!   * shapes no row of that matrix reaches — a bare `Field` on a multi-variant
//!     enum (every enum place in those extracted bodies downcasts first), and a
//!     payload read through a `Downcast` that disagrees with the discriminant on
//!     the path.

use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VariantDef, VerifiableBody, VerifiableFunction,
};

/// `resolve_field_scalar_range` in the `(width, signed)` spelling this matrix is
/// written in.
///
/// A `char` carrier is NOT folded into `None`: a decline emits no range fact
/// while `Char` emits the exact Unicode-scalar one, and a helper that returned
/// `None` for both would let a row about the DECLINE pass on the other answer.
/// No shape in this file reads a `char` payload, so the fold is a panic.
fn resolved_int(func: &VerifiableFunction, place: &Place) -> Option<(u32, bool)> {
    match super::type_ranges::resolve_field_scalar_range(func, place) {
        None => None,
        Some(crate::range::RustScalarRange::Integer { width, signed }) => Some((width, signed)),
        Some(crate::range::RustScalarRange::Char) => {
            panic!("no row in this file reads a `char` payload")
        }
    }
}

/// The range map's entry for `place`, in the same spelling.
fn mapped_int(func: &VerifiableFunction, place: &Place) -> Option<(u32, bool)> {
    match super::datatype_field_range_map(func).get(&crate::place_to_var_name(func, place)) {
        None => None,
        Some(crate::range::RustScalarRange::Integer { width, signed }) => Some((*width, *signed)),
        Some(crate::range::RustScalarRange::Char) => {
            panic!("no row in this file reads a `char` payload")
        }
    }
}

fn func_with_locals(name: &str, locals: Vec<LocalDecl>, return_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: name.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn variant(name: &str, field_ty: Option<Ty>, disc: i128) -> VariantDef {
    VariantDef {
        name: name.into(),
        discriminant: disc,
        fields: field_ty.into_iter().map(|t| ("0".to_string(), t)).collect(),
    }
}

/// `enum E { A(u8), B(u64) }` as the extractor lowers it: `variants` carries the
/// per-variant declared types and `fields` is the flat union view.
fn e_u8_u64() -> Ty {
    Ty::adt_enum(
        "E",
        vec![
            variant("A", Some(Ty::Int { width: 8, signed: false }), 0),
            variant("B", Some(Ty::Int { width: 64, signed: false }), 1),
        ],
    )
}

/// A function whose single statement copies `place` into local 0.
fn reads(name: &str, adt: Ty, place: Place) -> VerifiableFunction {
    let mut func = func_with_locals(
        name,
        vec![
            LocalDecl { index: 0, ty: Ty::Int { width: 64, signed: false }, name: None },
            LocalDecl { index: 1, ty: adt, name: Some("e".into()) },
        ],
        Ty::Int { width: 64, signed: false },
    );
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(place)),
        span: SourceSpan::default(),
    });
    func
}

/// A `Downcast(v).Field(i)` read on a real Rust enum must resolve to VARIANT
/// v's declared field type — not to flat slot `i`, which for `Field(0)` is the
/// synthetic `__tag`.
#[test]
fn downcast_field_resolves_to_the_declared_variant_field_type() {
    for (v, want) in [(0usize, (8u32, false)), (1, (64, false))] {
        let place =
            Place { local: 1, projections: vec![Projection::Downcast(v), Projection::Field(0)] };
        let func = reads("reads_payload", e_u8_u64(), place.clone());
        assert_eq!(
            resolved_int(&func, &place),
            Some(want),
            "variant {v}'s payload must resolve to its own declared type"
        );
        assert_eq!(
            mapped_int(&func, &place),
            Some(want),
            "the range map must be keyed by the payload's var name with variant {v}'s width"
        );
    }
}

/// On the EXTRACTOR's own layout, slot 0 of the flat `fields` view is the
/// synthetic `__tag: i64` — so the old flat step answered every
/// `Downcast(v).Field(0)` with `i64`. That single wrong answer is what
/// false-refuted narrow payloads and FALSE-PROVED `u64` ones, and the resolved
/// type must no longer be it.
///
/// This has to run on a real fixture: `Ty::adt_enum` builds its flat view by
/// unioning the VARIANT field names, and every tuple variant names its field
/// `"0"`, so a hand-built enum has no `__tag` slot at all and could not show
/// the mis-resolution the extractor's layout produces.
#[test]
fn downcast_field_no_longer_resolves_to_the_synthetic_tag() {
    let func: VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/enum_payload_u64_overflow_mir.json"
    ))
    .expect("u64-payload fixture MIR must deserialize");
    let Some(Ty::Adt { fields, .. }) = crate::local_ty_ref(&func, 1) else {
        panic!("local 1 is the extracted enum")
    };
    assert_eq!(
        fields.first().map(|(n, t)| (n.as_str(), t.clone())),
        Some(("__tag", Ty::Int { width: 64, signed: true })),
        "this test is only meaningful while the extractor's flat view leads with \
         __tag: i64 — that is the type the old walk returned for Field(0)"
    );
    let place =
        Place { local: 1, projections: vec![Projection::Downcast(0), Projection::Field(0)] };
    assert_eq!(
        resolved_int(&func, &place),
        Some((64, false)),
        "the u64 payload must resolve UNSIGNED; the tag's (64, signed) range excludes \
         every value above i64::MAX and deletes the overflow witness"
    );
}

/// A BARE `Field` on a multi-variant enum must get NO bound.
///
/// This is not conservatism for its own sake. Without a `Downcast` there is no
/// variant to read a declared type FROM. The flat step answers `Field(0)` with
/// the synthetic `__tag` — the wrong bound this walk exists to stop emitting —
/// and resolving it through variant 0 instead, the way the `Ty::Datatype` arm
/// resolves a single-variant datatype, would state variant 0's declared type
/// about a slot that is not variant 0's payload.
///
/// It costs the payload reads nothing, because the var name carries the
/// downcast: `place_to_var_name` spells `Downcast(v)` as `@v`, so `e@0.0` and
/// `e.0` are different SMT vars and withholding a bound from the second leaves
/// the first exactly as bounded.
#[test]
fn bare_field_on_multivariant_adt_enum_is_unbounded() {
    let place = Place { local: 1, projections: vec![Projection::Field(0)] };
    let func = reads("reads_flat_slot", e_u8_u64(), place.clone());
    assert_eq!(
        resolved_int(&func, &place),
        None,
        "a bare Field on a multi-variant enum names the flat aggregate slot every \
         variant's payload is written to; no variant's declared type bounds it"
    );
    assert!(
        !super::datatype_field_range_map(&func)
            .contains_key(&crate::place_to_var_name(&func, &place)),
        "and it must therefore not appear in the range map at all"
    );
}

/// A single-variant enum still requires the `Downcast`.
///
/// The `Ty::Datatype` arm resolves a bare `Field` through variant 0 when there
/// is only one variant; the `Ty::Adt` arm deliberately does not, because the
/// flat name is written by the aggregate lowering rather than by a variant
/// projection. rustc emits `Downcast(0)` for single-variant enums too, so
/// nothing real loses a bound.
#[test]
fn bare_field_on_single_variant_adt_enum_is_unbounded() {
    let adt = Ty::adt_enum("One", vec![variant("A", Some(Ty::Int { width: 8, signed: false }), 0)]);
    let bare = Place { local: 1, projections: vec![Projection::Field(0)] };
    let downcast =
        Place { local: 1, projections: vec![Projection::Downcast(0), Projection::Field(0)] };
    let func = reads("one_variant", adt, bare.clone());
    assert_eq!(resolved_int(&func, &bare), None);
    assert_eq!(
        resolved_int(&func, &downcast),
        Some((8, false)),
        "the downcast-qualified read still resolves"
    );
}

/// A STRUCT `Ty::Adt` has no `variants`, so it keeps the flat `project_ty` step
/// and its field bound is unchanged.
#[test]
fn struct_adt_field_resolution_is_unchanged() {
    let adt = Ty::adt("S", vec![("0".into(), Ty::Int { width: 8, signed: false })]);
    let place = Place { local: 1, projections: vec![Projection::Field(0)] };
    let func = reads("struct_field", adt, place.clone());
    assert_eq!(resolved_int(&func, &place), Some((8, false)));
}

/// The variant is chosen by the `Downcast` PROJECTION, never by a discriminant
/// the path condition happens to fix.
///
/// The model permits a body that switches on `discriminant(e) == 0` and then
/// reads `Downcast(1).Field(0)`. Safe Rust cannot write it, but if the lane
/// ever picked the variant from the path's discriminant instead of from the
/// projection, this read would be bounded by variant 0's `u8` while the name it
/// bounds is variant 1's `u64` slot — a false proof available to any hand-built
/// or future lowering. The read must keep variant 1's `u64`.
#[test]
fn downcast_wins_over_a_disagreeing_path_discriminant() {
    let place =
        Place { local: 1, projections: vec![Projection::Downcast(1), Projection::Field(0)] };
    let mut func = reads("wrong_variant_read", e_u8_u64(), place.clone());
    let disc = LocalDecl { index: 2, ty: Ty::Int { width: 64, signed: true }, name: None };
    func.body.locals.push(disc);
    func.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Discriminant(Place::local(1)),
            span: SourceSpan::default(),
        },
    );
    func.body.blocks[0].terminator = Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(2)),
        targets: vec![(0, BlockId(0))],
        otherwise: BlockId(0),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    assert_eq!(
        resolved_int(&func, &place),
        Some((64, false)),
        "the bound must follow the Downcast's variant, not the switched discriminant"
    );
}

/// The NESTED row's resolution, on the compiler's OWN extracted MIR.
///
/// `enum Inner { P(u8), Q } enum Outer { X(Inner), Y }` read as
/// `Downcast(0).Field(0).Downcast(0).Field(0)`. The verdict for this program is
/// PROVED before and after (rustc copies the read into a bare `u8` local first,
/// and that local's own type range already discharged it), so only the
/// resolution shows the change: the old walk stepped `Field(0)` to the outer
/// enum's `__tag: i64` and then failed to project `Field(0)` out of an integer,
/// yielding NO bound at all.
#[test]
fn nested_variant_payload_resolves_through_both_downcasts() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("../../tests/fixtures/enum_payload_nested_mir.json"))
            .expect("nested fixture MIR must deserialize");
    let place = Place {
        local: 1,
        projections: vec![
            Projection::Downcast(0),
            Projection::Field(0),
            Projection::Downcast(0),
            Projection::Field(0),
        ],
    };
    assert!(
        func.body.blocks.iter().any(|b| b.stmts.iter().any(|s| matches!(
            s,
            Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(p) | Operand::Move(p)), .. }
                if *p == place
        ))),
        "the fixture must actually contain the doubly-downcast read this test resolves"
    );
    assert_eq!(
        resolved_int(&func, &place),
        Some((8, false)),
        "the innermost payload's declared u8 must survive both downcasts"
    );
}

// ---------------------------------------------------------------------------
// FAIL-CLOSED: the enum decision may not be keyed on `variants` being present.
// ---------------------------------------------------------------------------

/// `Ty::Adt`'s FLAT ENUM VIEW as `trust-mir-extract::lower_enum_adt` builds it:
/// a leading synthetic `("__tag", isize)` slot followed by one
/// `__v{variant}_{field}` slot per variant field. `Ty::adt_enum` does NOT build
/// this shape (it unions the variant field NAMES), so a hand-built enum cannot
/// exhibit the mis-resolution the extractor's layout produces and these tests
/// have to spell the flat view out.
fn extractor_shaped_enum(variants: Vec<VariantDef>, variants_serialized: bool) -> Ty {
    let mut fields = vec![("__tag".to_string(), Ty::Int { width: 64, signed: true })];
    for (v, variant) in variants.iter().enumerate() {
        for (name, ty) in &variant.fields {
            fields.push((format!("__v{v}_{name}"), ty.clone()));
        }
    }
    let Ty::Adt { name, .. } =
        Ty::adt_enum("E", if variants_serialized { variants } else { Vec::new() })
    else {
        unreachable!("adt_enum builds an Adt")
    };
    Ty::Adt {
        name,
        fields,
        variants: if variants_serialized { unreachable!() } else { Vec::new() },
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: None,
        arbitrary_precision: None,
    }
}

/// A `Downcast(v).Field(0)` on an enum whose `variants` were ERASED by
/// `#[serde(default)]` must resolve to the payload's DECLARED type — read from
/// the `__v{v}_*` slot the erasure leaves behind — and never to `__tag`.
///
/// `Ty::Adt::variants` is `#[serde(default)]` on purpose, so every serialized
/// `Ty::Adt` older than PHASE 4 — dump fixtures, solver caches, proof
/// certificates — deserializes with an EMPTY list beside a RETAINED enum-shaped
/// flat view. Two answers are available on that shape and only one of them is
/// about the payload:
///
///   * flat slot `idx` — `__tag: i64` for every `Field(0)`. WRONG, and wrong in
///     the FALSE-PROOF direction for a `u64` payload: `i64`'s range excludes
///     every value above `i64::MAX`, which deletes the overflow witness. This is
///     what `project_ty` answers and what this lane exists to stop.
///   * the `idx`-th `__v{v}_`-prefixed slot — the payload's own declared type,
///     written there by the same `lower_enum_adt` loop that filled `variants`.
///     This is also what `crate::place_ty_cow` answers for this place.
///
/// The second is a real declaration, so declining here would drop a fact that is
/// available; the test pins that it is supplied, and pins it against the tag's
/// SIGNED range specifically, since that is the mis-resolution.
#[test]
fn variants_erased_by_serde_default_answers_the_payload_slot_not_the_tag() {
    let erased = extractor_shaped_enum(
        vec![variant("A", Some(Ty::Int { width: 64, signed: false }), 0)],
        false,
    );
    let Ty::Adt { fields, variants, .. } = &erased else { unreachable!() };
    assert!(variants.is_empty(), "this test is about the ERASED-variants shape");
    assert_eq!(
        fields.first().map(|(n, t)| (n.as_str(), t.clone())),
        Some(("__tag", Ty::Int { width: 64, signed: true })),
        "and about the flat view being RETAINED — that i64 is what the flat step \
         would answer for Field(0)"
    );
    let place =
        Place { local: 1, projections: vec![Projection::Downcast(0), Projection::Field(0)] };
    let func = reads("erased_variants", erased, place.clone());
    assert_eq!(
        resolved_int(&func, &place),
        Some((64, false)),
        "the payload's declared `u64` survives the erasure in the `__v0_0` slot; the \
         tag's (64, SIGNED) answer would delete every witness above i64::MAX"
    );
    assert_eq!(
        mapped_int(&func, &place),
        Some((64, false)),
        "and the range map must carry that unsigned width, not the tag's signed one"
    );
}

/// The erased shape with NO surviving declaration of the field still declines.
///
/// `enum E { A, B(u64) }` pre-P4 flattens to `[__tag, __v1_0]` — variant 0 has no
/// payload, so a `Downcast(0).Field(0)` has no `__v0_` slot AND no `variants`
/// entry. Flat slot 0 is `__tag: i64` and answering with it is exactly the
/// false-proof step; with both declarations silent the only sound answer is none.
#[test]
fn erased_variants_with_no_payload_slot_declines() {
    let erased = extractor_shaped_enum(
        vec![variant("A", None, 0), variant("B", Some(Ty::Int { width: 64, signed: false }), 1)],
        false,
    );
    let Ty::Adt { fields, .. } = &erased else { unreachable!() };
    assert_eq!(
        fields.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
        vec!["__tag", "__v1_0"],
        "variant 0 contributes no slot, so nothing declares its Field(0)"
    );
    let place =
        Place { local: 1, projections: vec![Projection::Downcast(0), Projection::Field(0)] };
    let func = reads("erased_no_payload", erased, place.clone());
    assert_eq!(resolved_int(&func, &place), None);
    assert!(
        !super::datatype_field_range_map(&func)
            .contains_key(&crate::place_to_var_name(&func, &place)),
        "and no range fact may be emitted for it"
    );
}

/// The `__v{v}_` prefix selects variant `v` and cannot be absorbed by a
/// higher-numbered variant that shares its digits.
///
/// `__v1_` is not a prefix of `__v11_0` (the character after `__v1` is a digit,
/// not the `_` the prefix requires), so a twelve-variant enum's variant 1 reads
/// its OWN payload. Without that the eleventh variant's `u64` would bound
/// variant 1's `u8` slot — an unsound narrowing in the other direction.
#[test]
fn payload_slot_prefix_does_not_absorb_a_longer_variant_index() {
    let mut variants: Vec<VariantDef> = (0..12)
        .map(|i| variant(&format!("V{i}"), Some(Ty::Int { width: 64, signed: false }), i as i128))
        .collect();
    variants[1] = variant("V1", Some(Ty::Int { width: 8, signed: false }), 1);
    let erased = extractor_shaped_enum(variants, false);
    for (v, want) in [(1usize, (8u32, false)), (11, (64, false))] {
        let place =
            Place { local: 1, projections: vec![Projection::Downcast(v), Projection::Field(0)] };
        let func = reads("erased_wide", erased.clone(), place.clone());
        assert_eq!(
            resolved_int(&func, &place),
            Some(want),
            "variant {v} must read its own __v{v}_0 slot"
        );
    }
}

/// With BOTH declarations present and DISAGREEING, the flat view wins — because
/// the flat view is the one `crate::place_ty_cow` types this place with.
///
/// `lower_enum_adt` fills the two views from one value, so a real extraction
/// cannot disagree; a hand-built or hand-edited `Ty::Adt` can. The range fact is
/// a statement about the var `place_to_var_name` mints for this place, and every
/// other fact about that var is derived from `place_ty`'s answer, so the bound
/// has to come from the same declaration `place_ty` reads or it is a statement
/// about a different type.
#[test]
fn flat_payload_slot_wins_over_a_disagreeing_variants_list() {
    let Ty::Adt { name, .. } = Ty::adt_enum("E", Vec::new()) else { unreachable!() };
    let adt = Ty::Adt {
        name,
        fields: vec![
            ("__tag".into(), Ty::Int { width: 64, signed: true }),
            ("__v0_0".into(), Ty::Int { width: 64, signed: false }),
        ],
        variants: vec![variant("A", Some(Ty::Int { width: 8, signed: false }), 0)],
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: None,
        arbitrary_precision: None,
    };
    let place =
        Place { local: 1, projections: vec![Projection::Downcast(0), Projection::Field(0)] };
    let func = reads("disagreeing_views", adt, place.clone());
    assert_eq!(
        crate::place_ty_cow(&func, &place).map(|t| t.into_owned()),
        Some(Ty::Int { width: 64, signed: false }),
        "place_ty resolves this place through the flat __v0_0 slot — that is the type \
         the rest of vcgen ascribes to the var this fact is attached to"
    );
    assert_eq!(
        resolved_int(&func, &place),
        Some((64, false)),
        "so the range must be u64's, not the variants list's u8 — a [0,255] bound on a \
         var everything else treats as u64 is a false proof"
    );
}

/// The same erased shape reached by a BARE `Field`, which under the flat step
/// would resolve slot 0 = `__tag: i64` just as directly.
#[test]
fn bare_field_on_a_variants_erased_enum_declines() {
    let erased = extractor_shaped_enum(
        vec![variant("A", Some(Ty::Int { width: 64, signed: false }), 0)],
        false,
    );
    let place = Place { local: 1, projections: vec![Projection::Field(0)] };
    let func = reads("erased_bare", erased, place.clone());
    assert_eq!(resolved_int(&func, &place), None);
}

/// The enum shape is ALSO recognised from `adt_kind`, with no synthetic field
/// names present at all.
///
/// `adt_kind` is stamped `Some(Enum)` by the extractor's enum arm and is a
/// second independent survivor of a `variants` erasure. Without this signal a
/// hand-built/`adt_enum`-shaped enum whose union view carries only real field
/// names would read as a struct on a bare `Field`.
#[test]
fn adt_kind_enum_alone_declines_a_bare_field() {
    let Ty::Adt { name, fields, .. } =
        Ty::adt_enum("E", vec![variant("A", Some(Ty::Int { width: 64, signed: false }), 0)])
    else {
        unreachable!()
    };
    assert!(
        fields.iter().all(|(n, _)| !n.starts_with("__")),
        "adt_enum's union view carries the variants' own field names, so this shape \
         has no synthetic marker and only `adt_kind` can classify it"
    );
    let kinded = Ty::Adt {
        name,
        fields,
        variants: Vec::new(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(trust_types::AdtKind::Enum),
        arbitrary_precision: None,
    };
    let place = Place { local: 1, projections: vec![Projection::Field(0)] };
    let func = reads("adt_kind_enum", kinded, place.clone());
    assert_eq!(resolved_int(&func, &place), None);
}

/// A `Downcast` pending over a type with NO variant structure declines too.
///
/// `project_ty` would answer `Field(i)` from the un-downcast view — for a
/// closure/coroutine frame that is upvar `i`, a different slot from state
/// variant `v`'s field `i`. Nothing in the walk may silently drop a pending
/// variant and answer from the flat view.
#[test]
fn a_pending_downcast_over_a_variantless_type_declines() {
    for ty in [
        Ty::Tuple(vec![Ty::Int { width: 8, signed: false }]),
        Ty::Closure {
            name: "c".into(),
            upvars: vec![Ty::Int { width: 8, signed: false }],
            call: None,
        },
    ] {
        let place =
            Place { local: 1, projections: vec![Projection::Downcast(0), Projection::Field(0)] };
        let func = reads("pending_downcast", ty.clone(), place.clone());
        assert_eq!(
            resolved_int(&func, &place),
            None,
            "{ty:?} has no variants; the un-downcast slot 0 is not variant 0's field 0"
        );
        // The same place WITHOUT the downcast still resolves — this is what
        // makes the assertion above about the pending variant and not about the
        // type being unresolvable.
        let bare = Place { local: 1, projections: vec![Projection::Field(0)] };
        let bare_func = reads("bare", ty.clone(), bare.clone());
        assert_eq!(resolved_int(&bare_func, &bare), Some((8, false)));
    }
}

/// A pending `Downcast` over a `Ty::Adt` carrying NO enum signal at all —
/// empty `variants`, `adt_kind: None`, no synthetic flat-view names — declines.
///
/// This is the one shape the `pending_variant.is_some()` disjunct decides on its
/// own: every other enum-shaped `Ty::Adt` is already caught by
/// `adt_shape_is_enum`. Without the disjunct the walk drops the pending variant
/// and answers with the STRUCT's slot 0, which is a different slot from variant
/// 0's field 0 whenever the two disagree. Mutation-checked: deleting the
/// disjunct passes every other test in this file and in
/// `tests/enum_payload_range.rs`, and fails only here.
#[test]
fn a_pending_downcast_over_a_signal_free_adt_declines() {
    let s = Ty::adt("S", vec![("0".into(), Ty::Int { width: 8, signed: false })]);
    let Ty::Adt { variants, adt_kind, fields, .. } = &s else { unreachable!() };
    assert!(
        variants.is_empty()
            && adt_kind.is_none()
            && fields.iter().all(|(n, _)| !n.starts_with("__")),
        "the point of this shape is that NO signal other than the pending Downcast \
         says `enum`"
    );
    let downcast =
        Place { local: 1, projections: vec![Projection::Downcast(0), Projection::Field(0)] };
    let func = reads("downcast_on_signal_free_adt", s.clone(), downcast.clone());
    assert_eq!(resolved_int(&func, &downcast), None);
    // The same place WITHOUT the downcast resolves, so the assertion above is
    // about the pending variant and not about the type being unresolvable.
    let bare = Place { local: 1, projections: vec![Projection::Field(0)] };
    let bare_func = reads("bare", s, bare.clone());
    assert_eq!(resolved_int(&bare_func, &bare), Some((8, false)));
}

/// A STRUCT whose flat view carries no synthetic names and no `adt_kind` still
/// resolves through the flat step — the fail-closed rule must not swallow the
/// ordinary struct-field bound (`struct_field_mul` is the verdict twin).
#[test]
fn a_plain_struct_still_resolves_through_the_flat_view() {
    for adt_kind in [None, Some(trust_types::AdtKind::Struct)] {
        let Ty::Adt { name, fields, .. } =
            Ty::adt("S", vec![("0".into(), Ty::Int { width: 8, signed: false })])
        else {
            unreachable!()
        };
        let s = Ty::Adt {
            name,
            fields,
            variants: Vec::new(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind,
            arbitrary_precision: None,
        };
        let place = Place { local: 1, projections: vec![Projection::Field(0)] };
        let func = reads("plain_struct", s, place.clone());
        assert_eq!(
            resolved_int(&func, &place),
            Some((8, false)),
            "adt_kind = {adt_kind:?}"
        );
    }
}
