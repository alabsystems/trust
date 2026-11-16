//! Wave 13, brief B: the bridge's type-shape recognizers.
//!
//! * ITER-RECV-1: the str-iterator state gate is positive, a `Zip` field is a
//!   scalar or a recognized slice iterator, and an `Enumerate` sits only over a
//!   base that yields at most `usize::MAX` items.
//! * TAG-FIELD-1: a `Struct`-stamped aggregate is built in declaration order
//!   whatever its field names, and the tag lane is the extractor's `__tag` on an
//!   ADT that can carry one.
//! * RATIO-DROP-1: drop totality comes from the compiler's `structural_drop` set,
//!   never from a `num_rational…::Ratio` name.
//!
//! Each "lie" assertion here was the opposite answer before the fix (stated per
//! test); the controls are the std shapes the recognizers exist for.

use super::*;

/// The receiver gate with the callee-side pattern check passing (`callee_str_patterns_are_core`
/// true), so each pin below exercises the TYPE gate alone.
fn str_receiver_with_core_patterns(ty: &Ty) -> bool {
    ty_is_str_iterator_receiver(ty, true)
}

fn adt(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    Ty::adt(name, fields.into_iter().map(|(field, ty)| (field.to_string(), ty)).collect())
}

fn usize64() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn int(width: u32, signed: bool) -> Ty {
    Ty::Int { width, signed }
}

fn ref_to(inner: Ty, mutable: bool) -> Ty {
    Ty::Ref { mutable, inner: Box::new(inner) }
}

fn str_bytes() -> Ty {
    // The verifier lane's `&str` (the `Slice { u8 }` conflation).
    ref_to(Ty::Slice { elem: Box::new(Ty::u8()) }, false)
}

/// A generic parameter as `trust-mir-extract` renders it (`TyKind::Param`).
fn type_param(name: &str) -> Ty {
    Ty::Unsupported { kind: "TyKind::Param".into(), detail: format!("generic parameter {name}") }
}

/// `core::slice::iter::Iter<'_, u8>` with its real field shape.
fn slice_iter_u8() -> Ty {
    adt(
        "core::slice::iter::Iter",
        vec![
            (
                "ptr",
                adt(
                    "core::ptr::non_null::NonNull",
                    vec![("pointer", Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) })],
                ),
            ),
            ("end_or_len", Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) }),
            ("_marker", adt("core::marker::PhantomData", vec![])),
        ],
    )
}

fn chars() -> Ty {
    adt("core::str::iter::Chars", vec![("iter", slice_iter_u8())])
}

/// `core::str::iter::Split<'_, P>` whose searcher state is `matcher`.
fn split_with_matcher(matcher: Ty) -> Ty {
    adt(
        "core::str::iter::Split",
        vec![(
            "0",
            adt(
                "core::str::iter::SplitInternal",
                vec![
                    ("start", usize64()),
                    ("end", usize64()),
                    ("matcher", matcher),
                    ("allow_trailing_empty", Ty::Bool),
                    ("finished", Ty::Bool),
                ],
            ),
        )],
    )
}

/// `CharPredicateSearcher<'_, F>`'s state: the predicate `F` itself, the
/// haystack and a `CharIndices`.
fn predicate_searcher(char_eq: Ty) -> Ty {
    adt(
        "core::str::pattern::CharPredicateSearcher",
        vec![(
            "0",
            adt(
                "core::str::pattern::MultiCharEqSearcher",
                vec![
                    ("char_eq", char_eq),
                    ("haystack", str_bytes()),
                    (
                        "char_indices",
                        adt(
                            "core::str::iter::CharIndices",
                            vec![("front_offset", usize64()), ("iter", chars())],
                        ),
                    ),
                ],
            ),
        )],
    )
}

/// `CharSearcher<'_>`, the searcher of a `char` pattern.
fn char_searcher() -> Ty {
    adt(
        "core::str::pattern::CharSearcher",
        vec![
            ("haystack", str_bytes()),
            ("finger", usize64()),
            ("finger_back", usize64()),
            ("needle", int(32, false)),
            ("utf8_size", Ty::u8()),
            ("utf8_encoded", Ty::Array { elem: Box::new(Ty::u8()), len: 4 }),
        ],
    )
}

// ─── ITER-RECV-1, str receivers ─────────────────────────────────────────────

/// The measured lie: `Split<'_, &mut F>` with a generic `F: FnMut(char) -> bool`.
/// `F` reaches the bridge as `Ref { Unsupported(TyKind::Param) }`; the former
/// negative walks answered "no closure, no non-std ADT" for it.
#[test]
fn str_split_over_a_generic_predicate_is_not_a_total_receiver() {
    let lie = split_with_matcher(predicate_searcher(ref_to(type_param("F"), true)));
    // The hole, stated: the closure probe alone says "no closure here".
    assert!(!ty_carries_closure_pattern(&lie), "precondition of this pin changed");
    assert!(!str_receiver_with_core_patterns(&lie), "a generic predicate may panic in `next`");
    assert!(!str_receiver_with_core_patterns(&ref_to(lie, true)));
}

#[test]
fn str_split_over_dyn_marker_float_or_closure_state_is_not_total() {
    let dyn_pattern =
        ref_to(Ty::Dynamic { trait_name: "core::ops::FnMut".into(), principal_key: None }, true);
    let boxed_dyn = adt(
        "alloc::boxed::Box",
        vec![(
            "0",
            Ty::RawPtr {
                mutable: false,
                pointee: Box::new(Ty::Dynamic {
                    trait_name: "core::ops::FnMut".into(),
                    principal_key: None,
                }),
            },
        )],
    );
    let marker = Ty::Datatype { name: "core::str::pattern::Hidden".into(), variants: vec![] };
    let closure = Ty::Closure { name: "m::f::{closure#0}".into(), upvars: vec![], call: None };
    for (label, state) in [
        ("&mut dyn FnMut", dyn_pattern),
        ("Box<dyn FnMut>", boxed_dyn),
        ("a bare Datatype marker", marker),
        ("a float", Ty::Float { width: 64 }),
        ("a closure", closure),
        ("a user ADT", adt("my_crate::Pattern", vec![("x", usize64())])),
    ] {
        let split = split_with_matcher(predicate_searcher(state));
        assert!(!str_receiver_with_core_patterns(&split), "{label} must fail the positive gate");
    }
}

#[test]
fn std_char_and_str_patterns_and_plain_str_iterators_stay_total() {
    assert!(str_receiver_with_core_patterns(&split_with_matcher(char_searcher())));
    let str_searcher = adt(
        "core::str::pattern::StrSearcher",
        vec![
            ("haystack", str_bytes()),
            ("needle", str_bytes()),
            (
                "searcher",
                adt(
                    "core::str::pattern::StrSearcherImpl",
                    vec![
                        ("__tag", Ty::i64()),
                        (
                            "__v0_0",
                            adt(
                                "core::str::pattern::EmptyNeedle",
                                vec![("position", usize64()), ("is_finished", Ty::Bool)],
                            ),
                        ),
                    ],
                ),
            ),
        ],
    );
    assert!(str_receiver_with_core_patterns(&split_with_matcher(str_searcher)));
    // `[char; N]` patterns keep a `char` array in their searcher.
    let char_array = adt(
        "core::str::pattern::CharArraySearcher",
        vec![(
            "0",
            adt(
                "core::str::pattern::MultiCharEqSearcher",
                vec![
                    ("char_eq", Ty::Array { elem: Box::new(int(32, false)), len: 3 }),
                    ("haystack", str_bytes()),
                ],
            ),
        )],
    );
    assert!(str_receiver_with_core_patterns(&split_with_matcher(char_array)));
    assert!(str_receiver_with_core_patterns(&chars()));
    assert!(str_receiver_with_core_patterns(&ref_to(chars(), true)));
    // A str iterator yields at most `len + 1` items: no `Enumerate` bound needed.
    // (The str-side adapter arm matches the two-segment `iter::Enumerate` spelling.)
    let enumerate_chars =
        adt("core::iter::Enumerate", vec![("iter", chars()), ("count", usize64())]);
    assert!(str_receiver_with_core_patterns(&enumerate_chars));
}

// ─── ITER-RECV-1, slice receivers: `Enumerate` ───────────────────────────────

fn range(name: &str, elem: Ty) -> Ty {
    if name.ends_with("RangeInclusive") {
        adt(name, vec![("start", elem.clone()), ("end", elem), ("exhausted", Ty::Bool)])
    } else {
        adt(name, vec![("start", elem.clone()), ("end", elem)])
    }
}

fn range_ex(elem: Ty) -> Ty {
    range("core::ops::range::Range", elem)
}

fn range_in(elem: Ty) -> Ty {
    range("core::ops::range::RangeInclusive", elem)
}

fn enumerate_with_count(inner: Ty, count: Ty) -> Ty {
    adt("core::iter::adapters::enumerate::Enumerate", vec![("iter", inner), ("count", count)])
}

fn enumerate(inner: Ty) -> Ty {
    enumerate_with_count(inner, usize64())
}

fn wrap(adapter: &str, inner: Ty) -> Ty {
    let scalar = match adapter {
        "core::iter::adapters::skip::Skip" | "core::iter::adapters::take::Take" => {
            vec![("n", usize64())]
        }
        _ => vec![],
    };
    let mut fields = vec![("iter", inner)];
    fields.extend(scalar);
    adt(adapter, fields)
}

const SKIP: &str = "core::iter::adapters::skip::Skip";
const TAKE: &str = "core::iter::adapters::take::Take";
const PEEKABLE: &str = "core::iter::adapters::peekable::Peekable";
const REV: &str = "core::iter::adapters::rev::Rev";

/// The measured lie: `(0u128..u128::MAX).enumerate().skip(usize::MAX).next()` was
/// certified and panicked `attempt to add with overflow` at enumerate.rs:96. Each
/// shape below was `true` before ITER-RECV-1.
#[test]
fn enumerate_over_a_range_wider_than_usize_is_not_total() {
    let wide = enumerate(range_ex(int(128, false)));
    assert!(!ty_is_slice_iterator_receiver(&wide));
    assert!(!ty_is_slice_iterator_receiver(&ref_to(wide.clone(), true)));
    for adapter in [SKIP, TAKE, PEEKABLE, REV] {
        assert!(!ty_is_slice_iterator_receiver(&wrap(adapter, wide.clone())), "{adapter}");
    }
    assert!(!ty_is_slice_iterator_receiver(&enumerate(range_ex(int(128, true)))));
    // `RangeInclusive<IntN>` yields up to `2^N` items: `0u64..=u64::MAX` overflows a
    // 64-bit count at `nth(usize::MAX)`.
    assert!(!ty_is_slice_iterator_receiver(&enumerate(range_in(int(64, false)))));
    // Nested: the outer `Enumerate` counts exactly what the inner yields.
    assert!(!ty_is_slice_iterator_receiver(&enumerate(enumerate(range_ex(int(128, false))))));
}

#[test]
fn enumerate_over_ranges_within_usize_and_over_containers_stays_total() {
    for elem in [int(8, false), int(32, false), int(32, true), int(64, false), int(64, true)] {
        assert!(ty_is_slice_iterator_receiver(&enumerate(range_ex(elem.clone()))), "{elem:?}");
    }
    for elem in [int(8, false), int(32, false), int(32, true), int(63, false)] {
        assert!(ty_is_slice_iterator_receiver(&enumerate(range_in(elem.clone()))), "{elem:?}");
    }
    assert!(ty_is_slice_iterator_receiver(&enumerate(slice_iter_u8())));
    assert!(ty_is_slice_iterator_receiver(&wrap(SKIP, enumerate(slice_iter_u8()))));
    assert!(ty_is_slice_iterator_receiver(&enumerate(adt(
        "alloc::collections::btree::map::Iter",
        vec![("length", usize64())],
    ))));
    // `Take` yields at most its `n: usize` items whatever it wraps.
    assert!(ty_is_slice_iterator_receiver(&enumerate(wrap(TAKE, range_ex(int(128, false))))));
    // Without an `Enumerate` nothing counts: a bare wide range stays a total base.
    assert!(ty_is_slice_iterator_receiver(&range_ex(int(128, false))));
    assert!(ty_is_slice_iterator_receiver(&wrap(SKIP, range_ex(int(128, false)))));
    assert!(ty_is_slice_iterator_receiver(&range_in(int(64, false))));
}

/// The `usize` width comes from the `Enumerate`'s own `count` field, so a 32-bit
/// target's `usize` (`Int { width: 32 }`) tightens the rule, and the faithful
/// lane's width-erased `PtrSizedInt` admits only container bases.
#[test]
fn enumerate_range_rule_reads_the_usize_width_from_its_count_field() {
    let count32 = int(32, false);
    assert!(ty_is_slice_iterator_receiver(&enumerate_with_count(
        range_ex(int(32, false)),
        count32.clone()
    )));
    assert!(!ty_is_slice_iterator_receiver(&enumerate_with_count(
        range_in(int(32, false)),
        count32.clone()
    )));
    assert!(!ty_is_slice_iterator_receiver(&enumerate_with_count(
        range_ex(int(64, false)),
        count32
    )));
    let erased = Ty::PtrSizedInt { signed: false };
    assert!(!ty_is_slice_iterator_receiver(&enumerate_with_count(
        range_ex(int(8, false)),
        erased.clone()
    )));
    assert!(ty_is_slice_iterator_receiver(&enumerate_with_count(slice_iter_u8(), erased)));
    // No `count` field at all: no witness, ranges refused, containers kept.
    let no_count =
        adt("core::iter::adapters::enumerate::Enumerate", vec![("iter", range_ex(int(8, false)))]);
    assert!(!ty_is_slice_iterator_receiver(&no_count));
}

#[test]
fn enumerate_over_read_dir_is_not_total_but_read_dir_alone_is() {
    let read_dir = adt("std::fs::ReadDir", vec![]);
    assert!(ty_is_slice_iterator_receiver(&read_dir));
    assert!(!ty_is_slice_iterator_receiver(&enumerate(read_dir)));
}

// ─── ITER-RECV-1, slice receivers: `Zip` ─────────────────────────────────────

fn zip(a: Ty, b: Ty) -> Ty {
    adt(
        "core::iter::adapters::zip::Zip",
        vec![("a", a), ("b", b), ("index", usize64()), ("len", usize64()), ("a_len", usize64())],
    )
}

/// The measured lie: `Zip<slice::Iter<u8>, &mut I>` with a generic `I: Iterator`
/// was certified; the inner's `next` panicked. `ty_is_iterator_shaped` treated
/// only ADTs as iterators, so the `Ref { Unsupported }` field was skipped as
/// "scalar state". Each shape below was `true` before ITER-RECV-1.
#[test]
fn zip_with_a_generic_dyn_or_unknown_inner_is_not_total() {
    let generic = ref_to(type_param("I"), true);
    assert!(!ty_is_slice_iterator_receiver(&zip(slice_iter_u8(), generic.clone())));
    assert!(!ty_is_slice_iterator_receiver(&zip(generic, slice_iter_u8())));
    let dyn_iter = ref_to(
        Ty::Dynamic { trait_name: "core::iter::Iterator".into(), principal_key: None },
        true,
    );
    assert!(!ty_is_slice_iterator_receiver(&zip(slice_iter_u8(), dyn_iter)));
    let marker = Ty::Datatype { name: "m::Hidden".into(), variants: vec![] };
    assert!(!ty_is_slice_iterator_receiver(&zip(slice_iter_u8(), marker)));
    assert!(!ty_is_slice_iterator_receiver(&zip(slice_iter_u8(), Ty::Float { width: 64 })));
}

#[test]
fn zip_of_two_slice_iterators_stays_total() {
    assert!(ty_is_slice_iterator_receiver(&zip(slice_iter_u8(), slice_iter_u8())));
    assert!(ty_is_slice_iterator_receiver(&zip(slice_iter_u8(), ref_to(slice_iter_u8(), true))));
    assert!(ty_is_slice_iterator_receiver(&zip(slice_iter_u8(), range_ex(int(128, false)))));
    // Under an `Enumerate` every inner must also meet the yield bound.
    assert!(ty_is_slice_iterator_receiver(&enumerate(zip(slice_iter_u8(), slice_iter_u8()))));
    assert!(!ty_is_slice_iterator_receiver(&enumerate(zip(
        slice_iter_u8(),
        range_ex(int(128, false))
    ))));
}

// ─── TAG-FIELD-1 ────────────────────────────────────────────────────────────

fn stamped(name: &str, fields: Vec<(&str, Ty)>, kind: Option<trust_types::AdtKind>) -> Ty {
    let mut ty = adt(name, fields);
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = kind;
    }
    ty
}

/// One function: `_0 = <dest_ty> { operands… }` built with `kind`, parameters
/// `_1..=_n` all `i64`.
fn aggregate_fn(
    dest_ty: Ty,
    kind: AggregateKind,
    operands: Vec<Operand>,
    params: usize,
) -> VerifiableFunction {
    let mut locals = vec![trust_types::LocalDecl { index: 0, ty: dest_ty.clone(), name: None }];
    locals.extend((1..=params).map(|index| trust_types::LocalDecl {
        index,
        ty: Ty::i64(),
        name: Some(format!("p{index}")),
    }));
    VerifiableFunction {
        name: "build".into(),
        def_path: "tag_field::build".into(),
        span: trust_types::SourceSpan::default(),
        body: trust_types::VerifiableBody {
            locals,
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(kind, operands),
                    span: trust_types::SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: params,
            return_ty: dest_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn adt_kind_agg(name: &str, variant: usize, active_field: Option<usize>) -> AggregateKind {
    AggregateKind::Adt { name: name.into(), variant, active_field, args: None }
}

fn copies(count: usize) -> Vec<Operand> {
    (1..=count).map(|index| Operand::Copy(Place::local(index))).collect()
}

/// `(field index, written value)` for every lane the function's aggregate
/// constructions write: each `InsertField`, and each lane of a complete
/// `MakeAggregate` constructor in lane order.
fn insertions(module: &trust_ir::Module) -> Vec<(u32, ValueId)> {
    module.functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .flat_map(|node| match &node.inst {
            Inst::InsertField { field, value, .. } => vec![(*field, *value)],
            Inst::MakeAggregate { fields, .. } => {
                fields.iter().enumerate().map(|(lane, value)| (lane as u32, *value)).collect()
            }
            _ => Vec::new(),
        })
        .collect()
}

fn entry_params(module: &trust_ir::Module) -> Vec<ValueId> {
    let function = &module.functions[0];
    let entry = function.blocks.iter().find(|block| block.id == function.entry).expect("entry");
    entry.params.iter().map(|(value, _)| *value).collect()
}

/// The measured lie: `S { tag: black_box(a), x: b }` on the VERIFIER lane, where
/// the extractor leaves `layout: None`. Before TAG-FIELD-1 this struct took the
/// flat-enum loop: `tag`/`discriminant`/`__tag` received the constant `0` and the
/// operands shifted one field left.
#[test]
fn verifier_lane_struct_fields_named_like_a_tag_take_their_own_operands() {
    for names in [["tag", "x"], ["discriminant", "x"], ["__tag", "x"], ["x", "tag"]] {
        let dest = stamped(
            "tag_field::S",
            names.iter().map(|name| (*name, Ty::i64())).collect(),
            Some(trust_types::AdtKind::Struct),
        );
        let func = aggregate_fn(dest, adt_kind_agg("tag_field::S", 0, None), copies(2), 2);
        let module = lower_to_trust_ir(&func).expect("a struct aggregate lowers");
        let params = entry_params(&module);
        assert_eq!(
            insertions(&module),
            vec![(0, params[0]), (1, params[1])],
            "{names:?}: every field takes its own operand, in declaration order"
        );
    }
}

#[test]
fn union_aggregate_without_an_active_field_is_refused() {
    let dest = stamped(
        "tag_field::U",
        vec![("tag", Ty::i64()), ("x", Ty::i64())],
        Some(trust_types::AdtKind::Union),
    );
    let func = aggregate_fn(dest, adt_kind_agg("tag_field::U", 0, None), copies(1), 1);
    let error = lower_to_trust_ir(&func).expect_err("a union needs an active field");
    assert!(error.to_string().contains("carries no active field"), "{error:?}");
}

/// On an enum (or an unstamped synthetic ADT) only `__tag` is the tag lane; a
/// payload field that happens to be NAMED `tag` takes its operand. Before
/// TAG-FIELD-1 the `tag` payload got the variant constant and the operand was
/// dropped.
#[test]
fn only_the_extractor_tag_name_is_a_tag_lane_on_an_enum() {
    for kind in [Some(trust_types::AdtKind::Enum), None] {
        let dest = stamped("tag_field::E", vec![("__tag", Ty::i64()), ("tag", Ty::i64())], kind);
        let func = aggregate_fn(dest, adt_kind_agg("tag_field::E", 0, None), copies(1), 1);
        let module = lower_to_trust_ir(&func).expect("an enum aggregate lowers");
        let inserted = insertions(&module);
        let params = entry_params(&module);
        assert_eq!(inserted.len(), 2, "{kind:?}: {inserted:?}");
        assert_eq!(inserted[1], (1, params[0]), "{kind:?}: the `tag` payload takes p1");
        assert_ne!(inserted[0].1, params[0], "{kind:?}: `__tag` holds the variant tag");
    }
}

#[test]
fn explicit_discriminant_field_is_the_extractor_tag_on_a_taggable_adt_only() {
    use trust_types::AdtKind;
    let tag_first = vec![("__tag", Ty::i64()), ("__v0_0", Ty::i64())];
    for kind in [Some(AdtKind::Enum), None] {
        let ty = stamped("m::E", tag_first.clone(), kind);
        assert_eq!(explicit_discriminant_field(&ty, "test").expect("tag lane").0, 0, "{kind:?}");
    }
    // A struct's or union's fields are the user's: never a tag lane, whatever the name.
    for kind in [AdtKind::Struct, AdtKind::Union] {
        for name in ["__tag", "tag", "discriminant", "__discriminant"] {
            let ty = stamped("m::S", vec![(name, Ty::i64())], Some(kind));
            assert!(explicit_discriminant_field(&ty, "test").is_err(), "{kind:?} {name}");
        }
    }
    // `tag`/`discriminant` are no longer tag names on any ADT.
    for name in ["tag", "discriminant", "__discriminant"] {
        let ty = stamped("m::E", vec![(name, Ty::i64())], None);
        assert!(explicit_discriminant_field(&ty, "test").is_err(), "{name}");
    }
}

// ─── RATIO-DROP-1 ───────────────────────────────────────────────────────────

fn drop_ok(ty: &Ty, structural: &[&str]) -> bool {
    let structural: FxHashSet<String> = structural.iter().map(|name| name.to_string()).collect();
    is_panic_free_drop_ext(ty, &structural, &FxHashSet::default(), &FxHashSet::default())
}

/// The measured lie: a dependency `num_rational_evil` with `struct Ratio { x: u8 }`
/// and a panicking `Drop` was proved drop-total (accepted under certify) because
/// its NAME matched `num_rational…::Ratio`. Both spellings were `true` before
/// RATIO-DROP-1.
#[test]
fn a_ratio_named_type_gets_no_drop_authority_from_its_name() {
    for name in ["num_rational_evil::Ratio", "num_rational::Ratio"] {
        let ratio = adt(name, vec![("x", Ty::u8())]);
        assert!(!drop_ok(&ratio, &[]), "{name}: not in structural_drop, so not credited");
        let datatype = Ty::Datatype {
            name: name.into(),
            variants: vec![("Ratio".into(), vec![("x".into(), Ty::u8())])],
        };
        assert!(!drop_ok(&datatype, &[]), "{name} (Datatype): not credited by name");
    }
}

#[test]
fn a_structural_ratio_walks_its_fields_in_both_spellings() {
    let real = adt("num_rational::Ratio", vec![("numer", Ty::i64()), ("denom", Ty::i64())]);
    assert!(drop_ok(&real, &["num_rational::Ratio"]));
    let datatype = Ty::Datatype {
        name: "num_rational::Ratio".into(),
        variants: vec![(
            "Ratio".into(),
            vec![("numer".into(), Ty::i64()), ("denom".into(), Ty::i64())],
        )],
    };
    assert!(drop_ok(&datatype, &["num_rational::Ratio"]));
    // The element still has to drop totally: an unstructural user element fails.
    let user = adt("my_crate::Panicky", vec![("x", Ty::i64())]);
    let ratio_user = adt("num_rational::Ratio", vec![("numer", user.clone()), ("denom", user)]);
    assert!(!drop_ok(&ratio_user, &["num_rational::Ratio"]));
    // A by-name marker shows no element and stays refused, structural or not.
    let marker = Ty::Datatype { name: "num_rational::Ratio".into(), variants: vec![] };
    assert!(!drop_ok(&marker, &["num_rational::Ratio"]));
    let empty_ctor = Ty::Datatype {
        name: "num_rational::Ratio".into(),
        variants: vec![("Ratio".into(), vec![])],
    };
    assert!(!drop_ok(&empty_ctor, &["num_rational::Ratio"]));
}
