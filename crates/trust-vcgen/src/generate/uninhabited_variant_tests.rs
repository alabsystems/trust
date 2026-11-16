//! Trust (UNINHABITED MATCH ARM, false REFUTATION): `inhabited_enum_variant_tag_set`
//! and the type-level uninhabitedness theorem it rests on.
//!
//! THE DEFECT. `match r { Ok(v) => .., Err(e) => match e {} }` over
//! `Result<u8, Infallible>` lowers to `_2 = Discriminant(r)` and a `SwitchInt` whose
//! `otherwise` edge is an `Unreachable` block. `Infallible` has NO inhabitants, so
//! that block is dead by construction and the code is CORRECT — yet the declared tag
//! set `{0, 1}` satisfies the block's path condition `_2 != 0` at `_2 = 1`, and the
//! `[unreach]` row was REFUTED, failing the user's build (measured at HEAD on
//! `Result<u8, Infallible>`, `Result<u8, Void>`, `Result<u8, !>`, a struct/tuple/array
//! payload carrying an uninhabited component, and an enum all of whose variants do).
//!
//! Every `true` from `ty_is_provably_uninhabited` DELETES a tag from a globally
//! published premise, so a wrong `true` is a FALSE PROOF — strictly worse than the
//! refutation being fixed. The `must decline` half of this file is therefore the
//! load-bearing half: `[Infallible; 0]` (exactly one value), a fieldless struct (the
//! empty product), a union (rustc holds unions always inhabited), anything behind a
//! pointer, an unresolved generic, and an un-migrated `adt_kind: None` ADT must all
//! keep their tag.
//!
//! MUTATION LEDGER, built and run rather than argued — every test here has at least
//! one mutant of the fix body that makes it fire:
//!
//!     NO-OP (declared set returned)  infallible_payload_*, transitively_*,
//!                                    a_wholly_uninhabited_source_*
//!     KEEP-TAG-0 (live tags deleted) zero_length_array_*, empty_products_*,
//!                                    partially_dead_enum_*, unresolvable_*,
//!                                    union_payload_declines, un_migrated_*,
//!                                    deep_nesting_*, a_wholly_uninhabited_source_*
//!     INVERTED (keep only the dead)  every test in the file except
//!                                    datatype_positional_tags_pass_through
//!     TYPE WIDENED (`[T; 0]` dead,   zero_length_array_*, union_payload_declines,
//!     unions as products,            un_migrated_adt_kind_declines
//!     `adt_kind: None` as enum)
//!     DATATYPE FILTERED              datatype_positional_tags_pass_through
//!     DEPTH FAILS OPEN               deep_nesting_fails_closed_to_inhabited
//!     EMPTY-SET GUARD REMOVED        a_wholly_uninhabited_source_publishes_no_fact
use trust_types::{
    AdtKind, BasicBlock, BlockId, Formula, LocalDecl, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VariantDef, VerifiableBody, VerifiableFunction,
};

/// `core::convert::Infallible` / `enum Void {}` exactly as `trust-mir-extract`'s
/// `lower_enum_adt` spells it: ZERO declared variants, `adt_kind: Some(Enum)`, and
/// the flattened `__tag` field the discriminant machinery reads.
fn void_enum(name: &str) -> Ty {
    Ty::Adt {
        name: name.into(),
        fields: vec![("__tag".into(), Ty::Int { width: 64, signed: true })].into(),
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(AdtKind::Enum),
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn struct_of(name: &str, fields: Vec<(String, Ty)>) -> Ty {
    Ty::Adt {
        name: name.into(),
        fields: fields.into(),
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(AdtKind::Struct),
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn enum_of(name: &str, variants: Vec<VariantDef>) -> Ty {
    Ty::Adt {
        name: name.into(),
        fields: vec![("__tag".into(), Ty::Int { width: 64, signed: true })].into(),
        variants: variants.into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(AdtKind::Enum),
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `Result<u8, E>` with the real `Ok = 0` / `Err = 1` tags.
fn result_u8(err_payload: Ty) -> Ty {
    enum_of(
        "core::result::Result",
        vec![
            VariantDef {
                name: "Ok".into(),
                discriminant: 0,
                fields: vec![("0".into(), Ty::Int { width: 8, signed: false })],
            },
            VariantDef {
                name: "Err".into(),
                discriminant: 1,
                fields: vec![("0".into(), err_payload)],
            },
        ],
    )
}

/// The tag set the discriminant range fact will publish for `Result<u8, payload>`.
fn result_tags(err_payload: Ty) -> Vec<i128> {
    super::inhabited_enum_variant_tag_set(&result_u8(err_payload))
        .expect("Result is a modeled 2-variant enum")
}

/// `fn f(r: Result<u8, P>) { _2 = Discriminant(r); switch _2 { 0 => bb2, _ => bb1 } }`
/// with `bb1` the `Unreachable` arm — the exact lowering of
/// `match r { Ok(v) => .., Err(e) => match e {} }`.
fn func_matching_result(err_payload: Ty) -> VerifiableFunction {
    let mut func = VerifiableFunction {
        name: "void_003".into(),
        def_path: "t::void_003".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Int { width: 8, signed: false }, name: None },
                LocalDecl { index: 1, ty: result_u8(err_payload), name: Some("r".into()) },
                LocalDecl { index: 2, ty: Ty::Int { width: 64, signed: true }, name: None },
            ],
            blocks: vec![
                BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
            ],
            arg_count: 1,
            return_ty: Ty::Int { width: 8, signed: false },
            datatype_defs: trust_types::DatatypeDefs::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: trust_types::FunctionSpec::default(),
        tuple_layouts: Default::default(),
    };
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Discriminant(Place::local(1)),
        span: SourceSpan::default(),
    });
    func
}

/// Every membership tag the fact builder publishes for the `Discriminant` read.
fn published_tags(func: &VerifiableFunction) -> Vec<Vec<i128>> {
    fn tags_of(f: &Formula, out: &mut Vec<i128>) {
        match f {
            Formula::Or(cases) => cases.iter().for_each(|c| tags_of(c, out)),
            Formula::Eq(_, rhs) => {
                if let Formula::Int(t) = rhs.as_ref() {
                    out.push(*t);
                }
            }
            _ => {}
        }
    }
    super::build_discriminant_variant_range_facts(func)
        .iter()
        .map(|f| {
            let mut out = Vec::new();
            tags_of(f, &mut out);
            out
        })
        .collect()
}

// ── the FIX: a provably-uninhabited payload loses its tag ────────────────────

/// THE FIXTURE. `Result<u8, Infallible>`: the `Err` tag must be GONE, so the fact
/// pins `_2 == 0` and refutes the `Unreachable` block's `_2 != 0` path condition.
#[test]
fn infallible_payload_drops_its_variant_tag() {
    assert_eq!(result_tags(void_enum("core::convert::Infallible")), vec![0]);
    let func = func_matching_result(void_enum("core::convert::Infallible"));
    let published = published_tags(&func);
    assert!(!published.is_empty(), "the discriminant read must still publish a fact");
    for tags in &published {
        assert_eq!(
            tags,
            &vec![0],
            "every published membership must pin the discriminant to the ONLY inhabited \
             variant; a surviving `= 1` is the false refutation: {published:?}"
        );
    }
}

/// The same for the four TRANSITIVE shapes and the primitive `!`. Each payload has no
/// inhabitant, so `Err` cannot occur.
#[test]
fn transitively_uninhabited_payloads_drop_their_variant_tag() {
    let void = || void_enum("t::Void");
    for (label, payload) in [
        ("the primitive `!`", Ty::Never),
        ("a struct with an uninhabited field", struct_of("t::Wrap", vec![("0".into(), void())])),
        ("a tuple with an uninhabited element", Ty::Tuple(vec![Ty::Bool, void()])),
        (
            "an array of length 1 over an uninhabited element",
            Ty::Array { elem: Box::new(void()), len: 1 },
        ),
        (
            "an array of length 7 over an uninhabited element",
            Ty::Array { elem: Box::new(void()), len: 7 },
        ),
        (
            "an enum all of whose variants carry an uninhabited field",
            enum_of(
                "t::AllDead",
                vec![
                    VariantDef {
                        name: "A".into(),
                        discriminant: 0,
                        fields: vec![("0".into(), void())],
                    },
                    VariantDef {
                        name: "B".into(),
                        discriminant: 1,
                        fields: vec![("0".into(), void())],
                    },
                ],
            ),
        ),
        (
            "a struct nesting all of the above",
            struct_of(
                "t::Deep",
                vec![
                    ("a".into(), Ty::Int { width: 8, signed: false }),
                    (
                        "b".into(),
                        Ty::Tuple(vec![struct_of("t::Inner", vec![("0".into(), void())])]),
                    ),
                ],
            ),
        ),
    ] {
        assert_eq!(result_tags(payload), vec![0], "{label} must drop the `Err` tag");
    }
}

// ── MUST DECLINE: an inhabited (or unresolvable) payload keeps its tag ───────

/// `[T; 0]` holds EXACTLY ONE value — the empty array — however dead `T` is. Reading
/// it as uninhabited would delete a REACHABLE arm's tag and bless UB there. The
/// length-1 twin above is the contrast that shows the rule is `len >= 1`, not "array".
#[test]
fn zero_length_array_stays_inhabited() {
    assert_eq!(
        result_tags(Ty::Array { elem: Box::new(void_enum("t::Void")), len: 0 }),
        vec![0, 1],
        "`[Void; 0]` is inhabited by the empty array; its `Err` tag must survive"
    );
}

/// A FIELDLESS struct is the empty PRODUCT — one value, inhabited. A fieldless enum
/// VARIANT (`None`) is likewise a nullary constructor and cannot empty its enum.
#[test]
fn empty_products_stay_inhabited() {
    assert_eq!(
        result_tags(struct_of("t::Unit0", vec![])),
        vec![0, 1],
        "a fieldless struct has exactly one value"
    );
    assert_eq!(
        result_tags(enum_of(
            "t::Opt",
            vec![
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), void_enum("t::Void"))],
                },
            ]
        )),
        vec![0, 1],
        "an enum with a NULLARY variant is inhabited even when every other variant is dead"
    );
}

/// One dead variant does not kill an enum that still has a live one.
#[test]
fn partially_dead_enum_stays_inhabited() {
    assert_eq!(
        result_tags(enum_of(
            "t::HalfDead",
            vec![
                VariantDef {
                    name: "A".into(),
                    discriminant: 0,
                    fields: vec![("0".into(), void_enum("t::Void"))],
                },
                VariantDef {
                    name: "B".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), Ty::Int { width: 8, signed: false })],
                },
            ]
        )),
        vec![0, 1]
    );
}

/// Everything the model cannot settle must DECLINE — a pointer to a dead type (the
/// pointee is never required to exist), an opaque/unresolved payload, a by-name
/// datatype reference, and an ADT whose `adt_kind` is the un-migrated `None` (where
/// `variants: []` is indistinguishable from a struct's spelling).
#[test]
fn unresolvable_and_indirect_payloads_decline() {
    let void = || void_enum("t::Void");
    for (label, payload) in [
        ("a shared reference", Ty::Ref { mutable: false, inner: Box::new(void()) }),
        ("a mutable reference", Ty::Ref { mutable: true, inner: Box::new(void()) }),
        ("a raw pointer", Ty::RawPtr { mutable: false, pointee: Box::new(void()) }),
        ("a slice (length unknown)", Ty::Slice { elem: Box::new(void()) }),
        (
            "a const-generic-length array",
            Ty::SymArray {
                elem: Box::new(void()),
                len_sym: trust_types::ConstLen { index: 0, name: "N".into() },
            },
        ),
        (
            "an unresolved generic parameter",
            Ty::Unsupported {
                kind: trust_types::PRE_MONO_ALIAS_KIND.into(),
                detail: trust_types::PRE_MONO_ALIAS_DETAIL.into(),
            },
        ),
        (
            "an opaque unsupported type",
            Ty::Unsupported { kind: "TyKind::Foreign".into(), detail: "extern type".into() },
        ),
        ("a by-name datatype reference", Ty::Datatype { name: "t::Void".into(), variants: vec![] }),
        ("a trait object", Ty::Dynamic { trait_name: "t::Tr".into(), principal_key: None }),
    ] {
        assert_eq!(result_tags(payload), vec![0, 1], "{label} must keep the `Err` tag");
    }
}

/// A UNION declines UNCONDITIONALLY: rustc itself holds unions always inhabited, and
/// their fields overlap rather than compose, so the product rule is not even the right
/// shape. `union U { a: ManuallyDrop<Infallible> }` is the fixture that would otherwise
/// be mis-read through the struct arm.
#[test]
fn union_payload_declines() {
    let u = Ty::Adt {
        name: "t::U".into(),
        fields: vec![("a".into(), void_enum("core::convert::Infallible"))].into(),
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(AdtKind::Union),
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    assert_eq!(result_tags(u), vec![0, 1], "a union is always inhabited");
}

/// `adt_kind: None` is the UN-MIGRATED spelling every hand-built and pre-W19
/// serialized `Ty::Adt` carries, and `variants: []` is ALSO how a struct is spelled.
/// Reading emptiness as "zero-variant enum" there would let a plain struct erase a
/// tag. This is the authority gate, and it must decline in BOTH directions: as the
/// payload under test, and as the enum whose tags are being published.
#[test]
fn un_migrated_adt_kind_declines() {
    let unkinded_void = Ty::Adt {
        name: "t::Void".into(),
        fields: vec![].into(),
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    assert_eq!(result_tags(unkinded_void), vec![0, 1]);
    // A hand-built enum (the pre-existing unit fixtures' spelling) is unaffected:
    // filtering reads the VARIANTS' field types, never the outer ADT's own kind.
    let hand_built = Ty::Adt {
        name: "t::E".into(),
        fields: vec![].into(),
        variants: vec![
            VariantDef { name: "A".into(), discriminant: 5, fields: vec![] },
            VariantDef { name: "B".into(), discriminant: 10, fields: vec![] },
        ]
        .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    assert_eq!(
        super::inhabited_enum_variant_tag_set(&hand_built),
        Some(vec![5, 10]),
        "a #[repr] enum's real non-contiguous tags must survive the filter untouched"
    );
}

/// A `Ty::Datatype`'s positional tag set is passed through UNFILTERED: its
/// empty-`variants` spelling is a by-name back-reference, so its structure is not read
/// for inhabitedness at all.
#[test]
fn datatype_positional_tags_pass_through() {
    let dt = Ty::Datatype {
        name: "clean_kernel::Expr".into(),
        variants: vec![
            ("App".into(), vec![]),
            ("Var".into(), vec![("0".into(), Ty::Never)]),
            ("Lam".into(), vec![]),
        ],
    };
    assert_eq!(super::inhabited_enum_variant_tag_set(&dt), Some(vec![0, 1, 2]));
}

/// When EVERY variant is uninhabited the filter empties the set — and the caller must
/// then publish NOTHING. These facts are GLOBAL to the function, so an empty
/// membership (the unsatisfiable `false`) would erase every overflow / bounds /
/// div-by-zero obligation in the body. Declining costs a proof; publishing `false`
/// would cost soundness.
#[test]
fn a_wholly_uninhabited_source_publishes_no_fact() {
    let all_dead = enum_of(
        "t::AllDead",
        vec![
            VariantDef {
                name: "A".into(),
                discriminant: 0,
                fields: vec![("0".into(), void_enum("t::Void"))],
            },
            VariantDef { name: "B".into(), discriminant: 1, fields: vec![("0".into(), Ty::Never)] },
        ],
    );
    assert_eq!(super::inhabited_enum_variant_tag_set(&all_dead), Some(vec![]));
    let mut func = func_matching_result(Ty::Int { width: 8, signed: false });
    func.body.locals[1].ty = all_dead;
    assert!(
        super::build_discriminant_variant_range_facts(&func).is_empty(),
        "an empty tag set must publish NO fact — never the unsatisfiable `false`"
    );
}

/// The walk is depth-bounded and fails closed. A nesting deeper than the budget
/// reports INHABITED (a lost proof), never uninhabited (a false proof).
#[test]
fn deep_nesting_fails_closed_to_inhabited() {
    let mut deep = void_enum("t::Void");
    for i in 0..64 {
        deep = struct_of(&format!("t::S{i}"), vec![("0".into(), deep)]);
    }
    assert_eq!(
        result_tags(deep),
        vec![0, 1],
        "exhausting the depth budget must answer INHABITED, the fail-closed direction"
    );
}

// ── RECURSIVE ENUMS: the source place is a bare by-name marker ───────────────

/// `T<NoExt>` with `enum T<X> { A, B(..), Ext(X) }` and `enum NoExt {}`, as
/// `lower_enum_adt` records a RECURSIVE enum's definition in the body's table.
fn recursive_t_definition(name: &str) -> Ty {
    enum_of(
        name,
        vec![
            VariantDef { name: "A".into(), discriminant: 0, fields: vec![] },
            VariantDef {
                name: "B".into(),
                discriminant: 1,
                fields: vec![(
                    "0".into(),
                    Ty::RawPtr {
                        mutable: false,
                        pointee: Box::new(Ty::Datatype { name: name.into(), variants: vec![] }),
                    },
                )],
            },
            VariantDef {
                name: "Ext".into(),
                discriminant: 2,
                fields: vec![("0".into(), void_enum("t::NoExt"))],
            },
        ],
    )
}

/// `fn f(t: &T<NoExt>) { _2 = Discriminant(*_1) }`, the scrutinee spelled as the
/// bare marker `name` and the table carrying `defs`.
fn func_matching_recursive_ref(name: &str, defs: Vec<Ty>) -> VerifiableFunction {
    let mut func = func_matching_result(Ty::Int { width: 8, signed: false });
    func.body.locals[1].ty = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Datatype { name: name.into(), variants: vec![] }),
    };
    for def in defs {
        assert!(trust_types::insert_datatype_def(&mut func.body.datatype_defs, def));
    }
    func.body.blocks[0].stmts.clear();
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Discriminant(Place {
            local: 1,
            projections: vec![trust_types::Projection::Deref],
        }),
        span: SourceSpan::default(),
    });
    func
}

/// THE RECURSIVE FIXTURE. The scrutinee is a bare marker the body's table defines:
/// the fact must be read off the DEFINITION, so the dead `Ext` tag is dropped and the
/// published membership is `{0, 1}`. Before `place_ty_resolved_cow`, NOTHING was
/// published (the marker has no variants), and `_2 = 2` refuted the dead arm.
#[test]
fn recursive_marker_scrutinee_reads_its_table_definition() {
    let name = "t::T<t::NoExt>";
    let func = func_matching_recursive_ref(name, vec![recursive_t_definition(name)]);
    let published = published_tags(&func);
    assert!(!published.is_empty(), "the discriminant read of a defined marker must publish");
    for tags in &published {
        assert_eq!(tags, &vec![0, 1], "the dead `Ext` tag must be dropped: {published:?}");
    }
}

/// FAIL CLOSED: a marker the table does NOT define — including one whose table entry
/// is for a DIFFERENT instantiation (`T<u8>` vs the scrutinee's `T<t::NoExt>`) —
/// publishes nothing, exactly as before the resolution existed. Binding a marker to a
/// same-family definition of another instantiation would type the body into the
/// wrong structure.
#[test]
fn undefined_or_other_instantiation_marker_publishes_no_fact() {
    let undefined = func_matching_recursive_ref("t::T<t::NoExt>", vec![]);
    assert!(super::build_discriminant_variant_range_facts(&undefined).is_empty());
    let other =
        func_matching_recursive_ref("t::T<t::NoExt>", vec![recursive_t_definition("t::T<u8>")]);
    assert!(
        super::build_discriminant_variant_range_facts(&other).is_empty(),
        "a table entry for another instantiation must not resolve this marker"
    );
}

// ── REPR-U128-HIGH-TAG-1: a lossy tag under an UNSIGNED read is no fact ──────

/// `#[repr(u128)] enum E { A = 0, B = u128::MAX, C = 5 }` exactly as the extractor
/// spelled it before REPR-U128-HIGH-TAG-1: `B`'s tag stored as the lossy
/// `u128::MAX as i128 == -1`. The extractor now lowers this enum to `Unsupported`;
/// a SERIALIZED body (an older dump) or a hand-built one can still carry it.
fn lossy_repr_u128_enum() -> Ty {
    enum_of(
        "t::E",
        vec![
            VariantDef { name: "A".into(), discriminant: 0, fields: vec![] },
            VariantDef { name: "B".into(), discriminant: -1, fields: vec![] },
            VariantDef { name: "C".into(), discriminant: 5, fields: vec![] },
        ],
    )
}

/// `fn p(e: E) { _2 = Discriminant(e) }` with `_2` declared `dest_ty`.
fn func_reading_lossy_tags_into(dest_ty: Ty) -> VerifiableFunction {
    let mut func = func_matching_result(Ty::Int { width: 8, signed: false });
    func.body.locals[1].ty = lossy_repr_u128_enum();
    func.body.locals[2].ty = dest_ty;
    func
}

/// Every name the published facts mention.
fn fact_names(facts: &[Formula]) -> Vec<String> {
    let mut names: Vec<String> =
        facts.iter().flat_map(|f| f.free_variables().into_iter()).collect();
    names.sort();
    names.dedup();
    names
}

/// THE FIX (defense in depth). A `u128` read cannot produce `-1`; the SwitchInt label
/// for `B` renders the true `u128::MAX`, so `_2 ∈ {0, -1, 5}` deleted the real tag and
/// made the `B` arm vacuous. No membership may be published — not over the dest, not
/// over the canonical `__trust_mir__discr_*` carrier (the same read) — and the same
/// for a `usize` (pointer-sized unsigned) read.
#[test]
fn negative_tag_read_into_an_unsigned_dest_publishes_no_fact() {
    for dest_ty in [Ty::Int { width: 128, signed: false }, Ty::PtrSizedInt { signed: false }] {
        let func = func_reading_lossy_tags_into(dest_ty.clone());
        let facts = super::build_discriminant_variant_range_facts(&func);
        assert!(
            facts.is_empty(),
            "{dest_ty:?}: a negative tag under an unsigned read is a FALSE membership; \
             published {facts:?} over {:?}",
            fact_names(&facts)
        );
        assert!(!super::discriminant_tags_denote_dest_values(&func, &Place::local(2), &[0, -1, 5]));
    }
}

/// CONTROL: the same tags read into a SIGNED dest are genuine (a `#[repr(i128)]` or
/// `repr(isize)` enum with a negative tag) and keep their fact, over the dest and
/// the canonical carrier, with `-1` in the set.
#[test]
fn negative_tag_read_into_a_signed_dest_keeps_its_fact() {
    for dest_ty in [Ty::Int { width: 128, signed: true }, Ty::PtrSizedInt { signed: true }] {
        let func = func_reading_lossy_tags_into(dest_ty.clone());
        let published = published_tags(&func);
        assert_eq!(published.len(), 2, "{dest_ty:?}: dest and carrier: {published:?}");
        for tags in &published {
            assert_eq!(tags, &vec![0, -1, 5], "{dest_ty:?}");
        }
        let names = fact_names(&super::build_discriminant_variant_range_facts(&func));
        assert!(
            names.iter().any(|n| n.starts_with("__trust_mir__discr_")),
            "{dest_ty:?}: the canonical carrier must be bound: {names:?}"
        );
    }
}

/// CONTROL (no capability loss): NON-negative tags mean the same number under every
/// integer type, so an unsigned read keeps its fact — `#[repr(u128)] { 0, 7, 5 }`.
#[test]
fn non_negative_tags_read_into_an_unsigned_dest_keep_their_fact() {
    let mut func = func_reading_lossy_tags_into(Ty::Int { width: 128, signed: false });
    func.body.locals[1].ty = enum_of(
        "t::E",
        vec![
            VariantDef { name: "A".into(), discriminant: 0, fields: vec![] },
            VariantDef { name: "B".into(), discriminant: 7, fields: vec![] },
            VariantDef { name: "C".into(), discriminant: 5, fields: vec![] },
        ],
    );
    let published = published_tags(&func);
    assert_eq!(published.len(), 2, "dest and carrier: {published:?}");
    for tags in &published {
        assert_eq!(tags, &vec![0, 7, 5]);
    }
}

/// FAIL CLOSED: a dest whose type does not resolve gives a negative tag no
/// denotation either.
#[test]
fn negative_tag_read_into_an_unresolvable_dest_publishes_no_fact() {
    let mut func = func_reading_lossy_tags_into(Ty::Int { width: 128, signed: true });
    func.body.blocks[0].stmts.clear();
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(9),
        rvalue: Rvalue::Discriminant(Place::local(1)),
        span: SourceSpan::default(),
    });
    assert!(super::build_discriminant_variant_range_facts(&func).is_empty());
}

/// The refutation lane's exact pin (`dest == __trust_mir__discr_<src>` plus the
/// carrier's membership) applies the same gate: no pin for the unsigned read, one pin
/// carrying `-1` for the signed control.
#[test]
fn discriminant_pin_declines_a_negative_tag_under_an_unsigned_dest() {
    let input_free: trust_types::fx::FxHashSet<usize> = [1].into_iter().collect();
    let stable: trust_types::fx::FxHashSet<String> = ["_2".to_string()].into_iter().collect();
    let unsigned = func_reading_lossy_tags_into(Ty::Int { width: 128, signed: false });
    assert_eq!(crate::place_to_var_name(&unsigned, &Place::local(2)), "_2");
    assert!(
        super::discriminant_pin_defs(&unsigned, &input_free, &stable).is_empty(),
        "no pin may carry the false membership onto a u128 dest"
    );
    let signed = func_reading_lossy_tags_into(Ty::Int { width: 128, signed: true });
    let pins = super::discriminant_pin_defs(&signed, &input_free, &stable);
    assert_eq!(pins.len(), 1, "the signed control keeps its pin");
    let mut tags = Vec::new();
    for range in &pins[0].1 {
        let Formula::Or(cases) = range else { panic!("membership over three tags: {range:?}") };
        for case in cases {
            if let Formula::Eq(_, rhs) = case
                && let Formula::Int(t) = rhs.as_ref()
            {
                tags.push(*t);
            }
        }
    }
    assert_eq!(tags, vec![0, -1, 5]);
}
