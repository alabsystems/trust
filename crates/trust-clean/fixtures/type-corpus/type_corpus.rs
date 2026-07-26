// trust-clean/fixtures/type-corpus/type_corpus.rs
//
// TYPE-REFLECTION COVERAGE corpus: every Rust type CONSTRUCTOR as a Trust MIR
// `trust_types::Ty`, paired with its Rust source form. The measurement test
// `type_corpus_coverage` (in `src/reflect.rs`'s test module, which `include!`s
// this file) reflects EACH entry through the type functor `reflect_ty` (plus the
// named-inductive `reflect_struct`/`reflect_enum` registration path) and
// classifies it:
//
//   * STRUCTURAL-modulo-3 — the type reflects to a real `Trust.SortTy` carrier
//     code whose `axiom_closure` (against `carrier_context()`) is a subset of the
//     3 foundational axioms {propext, Quot.sound, Classical.choice} AND references
//     no unresolved const, OR it registers as a real named inductive
//     (struct/enum/float/ptr/sink) that passes the real-kernel modulo-3
//     `register_adt_carriers` axiom gate.
//   * OPAQUE / UNROOTED — the type reflects to a free type-variable const
//     (`Trust.Param.*` / `Trust.Dyn.*` / `Trust.Opaque.*`) that is NOT declared in
//     `carrier_context()`, so its `axiom_closure` reports the const UNRESOLVED
//     (NOT rooted in the 3 — a soundness hole), OR it fails closed with a
//     `ReflectError`.
//
// This is a MEASUREMENT corpus (no engine change): it enumerates the surface and
// records the honest coverage map. The goal it measures is "EVERY Rust type is a
// Clean dependent type with axiom_deps ⊆ the 3".
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// NOTE: this file is `include!`d into `reflect.rs`'s `#[cfg(test)] mod tests`,
// which ALREADY brings `Ty` + `FnSig` (via `use super::*`) and `VariantDef` (via
// the module's own `use trust_types::VariantDef`) into scope. To avoid a
// double-import (E0252) this file `use`s NOTHING and references those three types
// by their already-in-scope bare names.

/// A bare generic type parameter `T` (`TyKind::Param`) as `trust-mir-extract`
/// lowers it: an `Unsupported{kind:"TyKind::Param", detail:"generic parameter
/// <name>/#<index> needs monomorphization"}`. The detail's `<name>/#<index>` is
/// the stable identity `reflect_ty` keys the `Trust.Param.<id>` const on.
fn param(name_idx: &str) -> Ty {
    Ty::Unsupported {
        kind: "TyKind::Param".into(),
        detail: format!("generic parameter {name_idx} needs monomorphization"),
    }
}

fn i32_ty() -> Ty {
    Ty::Int { width: 32, signed: true }
}

fn u8_ty() -> Ty {
    Ty::Int { width: 8, signed: false }
}

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

/// A monomorphized std container `Ty::Adt` as `trust-mir-extract` lowers it: the
/// def-path `name` plus the type-erased internal field tree. We model the common
/// recoverable shape — a buffer pointer/slice carrying the element — so
/// `reflect_known_container`'s element recovery fires.
fn container_adt(def_path: &str, elem: Ty) -> Ty {
    // A `RawVec`-style buffer struct whose pointer pointee IS the element, plus a
    // `len` slot (skipped by element recovery). This mirrors the monomorphized
    // `Vec`/`VecDeque` layout that `sequence_element_ty` walks.
    let buf = Ty::adt(
        "alloc::raw_vec::RawVec",
        vec![(
            "ptr".into(),
            Ty::RawPtr { mutable: true, pointee: Box::new(elem) },
        )],
    );
    Ty::adt(
        def_path,
        vec![("buf".into(), buf), ("len".into(), Ty::Int { width: 64, signed: false })],
    )
}

/// A transparent smart-pointer `Ty::Adt` (`Box`/`Rc`/`Arc`) over `inner`, in the
/// monomorphized `Unique<NonNull<T>>` shape `smart_pointer_inner_ty` walks.
fn smart_ptr_adt(def_path: &str, inner: Ty) -> Ty {
    let nonnull = Ty::adt(
        "core::ptr::non_null::NonNull",
        vec![(
            "pointer".into(),
            Ty::RawPtr { mutable: false, pointee: Box::new(inner) },
        )],
    );
    Ty::adt(def_path, vec![("pointer".into(), nonnull)])
}

/// A monomorphized `slice::Iter<T>` / `str::Chars` `Ty::Adt` as `trust-mir-extract`
/// lowers it: the type-erased `{ ptr : NonNull<*const T>, end_or_len : *const T,
/// _marker : PhantomData }` layout (the REAL shape observed in dumped MIR). The
/// element `T` is recoverable as the `ptr.pointer` pointee.
fn slice_iter_adt(def_path: &str, elem: Ty) -> Ty {
    let nonnull = Ty::adt(
        "std::ptr::NonNull",
        vec![(
            "pointer".into(),
            Ty::RawPtr { mutable: false, pointee: Box::new(elem.clone()) },
        )],
    );
    Ty::adt(
        def_path,
        vec![
            ("ptr".into(), nonnull),
            ("end_or_len".into(), Ty::RawPtr { mutable: false, pointee: Box::new(elem) }),
            ("_marker".into(), Ty::adt("std::marker::PhantomData", vec![])),
        ],
    )
}

/// A monomorphized iterator adapter wrapping a `source` iterator plus a `closure`
/// field (`Map<I,F>` / `Filter<I,P>`) as `trust-mir-extract` lowers it: `{ iter :
/// <source>, <fname> : <closure> }` (the REAL shape observed in dumped MIR).
fn iter_adapter_adt(def_path: &str, source: Ty, fname: &str, closure: Ty) -> Ty {
    Ty::adt(def_path, vec![("iter".into(), source), (fname.into(), closure)])
}

/// A `i32`-slice iterator source (`std::slice::Iter<i32>`), the common adapter base.
fn i32_slice_iter() -> Ty {
    slice_iter_adt("std::slice::Iter", i32_ty())
}

/// A monomorphized `HashMap<K,V>` / `BTreeMap<K,V>` whose recoverable `(K, V)`
/// entry tuple sits behind the `hashbrown::raw::Bucket` `NonNull<*const (K, V)>`
/// pointer (the REAL recoverable shape observed in dumped MIR — the `RawTable`
/// buckets are otherwise type-erased to `*const u8`). `map_kv_tys` walks the field
/// tree for the unique `(K, V)` 2-tuple pointee.
fn map_adt(def_path: &str, k: Ty, v: Ty) -> Ty {
    // The entry pointer carrying the `(K, V)` tuple, nested as the hashbrown layout
    // exposes it through a `Bucket`'s `NonNull<*const (K, V)>`.
    let entry_ptr = Ty::adt(
        "std::ptr::NonNull",
        vec![(
            "pointer".into(),
            Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Tuple(vec![k, v])) },
        )],
    );
    let bucket = Ty::adt("hashbrown::raw::Bucket", vec![("ptr".into(), entry_ptr)]);
    let table = Ty::adt(
        "hashbrown::raw::RawTable",
        vec![
            ("bucket".into(), bucket),
            ("items".into(), Ty::Int { width: 64, signed: false }),
        ],
    );
    Ty::adt(def_path, vec![("table".into(), table)])
}

/// The full type corpus: `(constructor_name, rust_source_form, Ty)`. One entry per
/// Rust type CONSTRUCTOR the goal must cover.
#[allow(clippy::too_many_lines)]
pub(crate) fn type_corpus() -> Vec<(&'static str, &'static str, Ty)> {
    let mut c: Vec<(&'static str, &'static str, Ty)> = Vec::new();

    // --- primitive integers (signed) ---
    c.push(("i8", "i8", Ty::Int { width: 8, signed: true }));
    c.push(("i16", "i16", Ty::Int { width: 16, signed: true }));
    c.push(("i32", "i32", Ty::Int { width: 32, signed: true }));
    c.push(("i64", "i64", Ty::Int { width: 64, signed: true }));
    c.push(("i128", "i128", Ty::Int { width: 128, signed: true }));
    // --- primitive integers (unsigned) ---
    c.push(("u8", "u8", Ty::Int { width: 8, signed: false }));
    c.push(("u16", "u16", Ty::Int { width: 16, signed: false }));
    c.push(("u32", "u32", Ty::Int { width: 32, signed: false }));
    c.push(("u64", "u64", Ty::Int { width: 64, signed: false }));
    c.push(("u128", "u128", Ty::Int { width: 128, signed: false }));

    // --- other scalars ---
    c.push(("bool", "bool", Ty::Bool));
    // `char` is a 32-bit scalar at the MIR level (a Unicode scalar value).
    c.push(("char", "char", Ty::Int { width: 32, signed: false }));
    c.push(("f32", "f32", Ty::Float { width: 32 }));
    c.push(("f64", "f64", Ty::Float { width: 64 }));
    c.push(("unit", "()", Ty::Unit));
    // NEVER (`!`) — the bottom type reflects to the EMPTY INDUCTIVE `Trust.Never`
    // (a 0-constructor `Type`, the Clean analogue of `False`/`Empty`), classified
    // STRUCTURAL-modulo-3 via the dedicated `never_grounds_modulo_3_real_kernel`
    // gate. Reflecting the TYPE does NOT require inhabiting it: the empty inductive
    // is uninhabited by construction, so VALUE inhabitation stays fail-closed. (The
    // `refine_never_fail_closed` probe below confirms a refinement OVER `!` — which
    // DOES need a witness carrier — still fails closed.)
    c.push(("never", "!", Ty::Never));

    // --- references / raw pointers ---
    c.push(("ref_shared", "&i32", Ty::Ref { mutable: false, inner: Box::new(i32_ty()) }));
    c.push(("ref_mut", "&mut i32", Ty::Ref { mutable: true, inner: Box::new(i32_ty()) }));
    c.push(("ptr_const", "*const i32", Ty::RawPtr { mutable: false, pointee: Box::new(i32_ty()) }));
    c.push(("ptr_mut", "*mut i32", Ty::RawPtr { mutable: true, pointee: Box::new(i32_ty()) }));

    // --- structs ---
    // named struct (all-concrete fields)
    c.push((
        "struct_named",
        "struct Point { x: i32, y: i32 }",
        Ty::adt("Point", vec![("x".into(), i32_ty()), ("y".into(), i32_ty())]),
    ));
    // tuple-struct (fields named 0,1)
    c.push((
        "struct_tuple",
        "struct Pair(i32, u8)",
        Ty::adt("Pair", vec![("0".into(), i32_ty()), ("1".into(), u8_ty())]),
    ));
    // unit-struct (no fields) — Prod/Unit floor (no Int content)
    c.push(("struct_unit", "struct Unit;", Ty::adt("UnitStruct", vec![])));
    // generic struct `Wrapper<T> { value: T }`
    c.push((
        "struct_generic",
        "struct Wrapper<T> { value: T }",
        Ty::adt("Wrapper", vec![("value".into(), param("T/#0"))]),
    ));

    // --- enums ---
    // C-like enum (fieldless variants) → a FAITHFUL, DISCRIMINANT-AWARE multi-
    // constructor inductive `Trust.Adt.Dir` (one NULLARY constructor per variant, each
    // with its discriminant tag), registered modulo 3 by `register_adt_carriers` (the
    // inductive + auto-derived recursor `axiom_deps` are EMPTY — NO 4th axiom). The
    // carrier is the nominal sum type, INJECTIVE: `Trust.Adt.Dir` is DISTINCT from any
    // struct's anonymous `Prod` and from any other enum's name, and the four variants are
    // DISTINCT constructors — NOT the pre-fix non-injective `reflect_struct_product` over
    // the union of variant fields (which flattened all four fieldless variants to `Unit`).
    c.push((
        "enum_c_like",
        "enum Dir { N, S, E, W }",
        Ty::adt_enum(
            "Dir",
            vec![
                VariantDef { name: "N".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "S".into(), discriminant: 1, fields: vec![] },
                VariantDef { name: "E".into(), discriminant: 2, fields: vec![] },
                VariantDef { name: "W".into(), discriminant: 3, fields: vec![] },
            ],
        ),
    ));
    // data enum (concrete payloads) → a FAITHFUL multi-constructor inductive
    // `Trust.Adt.Shape` whose `Circle(u32)` and `Rect { w, h }` are DISTINCT constructors
    // (Circle ≠ Rect, each carrying its own field arity and discriminant), registered
    // modulo 3 (inductive + recursor `axiom_deps` EMPTY — NO 4th axiom). DISTINCT from a
    // plain 3-field struct's `Prod`-of-3-`BitVec` — NOT the pre-fix non-injective
    // `reflect_struct_product` over the UNION `{0, w, h}` of variant fields, which
    // conflated `Shape` with a plain `struct(u32, u32, u32)` and erased the sum structure.
    c.push((
        "enum_data",
        "enum Shape { Circle(u32), Rect { w: u32, h: u32 } }",
        Ty::adt_enum(
            "Shape",
            vec![
                VariantDef {
                    name: "Circle".into(),
                    discriminant: 0,
                    fields: vec![("0".into(), Ty::Int { width: 32, signed: false })],
                },
                VariantDef {
                    name: "Rect".into(),
                    discriminant: 1,
                    fields: vec![
                        ("w".into(), Ty::Int { width: 32, signed: false }),
                        ("h".into(), Ty::Int { width: 32, signed: false }),
                    ],
                },
            ],
        ),
    ));
    // generic enum `MyEnum<T> { A(T), B }`
    c.push((
        "enum_generic",
        "enum MyEnum<T> { A(T), B }",
        Ty::adt_enum(
            "MyEnum",
            vec![
                VariantDef { name: "A".into(), discriminant: 0, fields: vec![("0".into(), param("T/#0"))] },
                VariantDef { name: "B".into(), discriminant: 1, fields: vec![] },
            ],
        ),
    ));

    // --- REAL-CODE COVERAGE: stdlib ERROR ENUMS / error structs ---
    // The report's residual-46 listed `ParseIntError`/`IntErrorKind`/`Utf8Error` as
    // "opaque error enums". They ARE plain ADTs — a C-like discriminant enum
    // (`IntErrorKind`) and thin structs wrapping it (`ParseIntError`) / scalar
    // fields (`Utf8Error`). These probes show the carrier grounds modulo 3 as a
    // FAITHFUL sum type / record: `IntErrorKind` is a 5-constructor inductive (each
    // fieldless variant a DISTINCT nullary constructor with its discriminant — NOT a
    // single flattened `Unit`), and `ParseIntError` / `Utf8Error` are single-`.mk`
    // RECORDS whose field GROUNDS OVER that nested faithful enum inductive (the
    // `IntErrorKind` / `Option<u8>` field decodes to the registered multi-ctor inductive,
    // not a `Prod`-flattened union). All are admitted by the SAME `register_adt_carriers`
    // axiom gate (inductive + recursor `axiom_deps` EMPTY — NO 4th axiom). The real-code
    // opacity is an EXTRACTION gap (the monomorphized MIR exposes the nominal type's
    // PRIVATE fields without the variant/field tree), NOT a carrier-modeling gap.
    // `IntErrorKind` — a C-like discriminant enum → a 5-constructor faithful inductive.
    c.push((
        "int_error_kind",
        "core::num::IntErrorKind { Empty, InvalidDigit, PosOverflow, NegOverflow, Zero }",
        Ty::adt_enum(
            "core::num::IntErrorKind",
            vec![
                VariantDef { name: "Empty".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "InvalidDigit".into(), discriminant: 1, fields: vec![] },
                VariantDef { name: "PosOverflow".into(), discriminant: 2, fields: vec![] },
                VariantDef { name: "NegOverflow".into(), discriminant: 3, fields: vec![] },
                VariantDef { name: "Zero".into(), discriminant: 4, fields: vec![] },
            ],
        ),
    ));
    // `ParseIntError { kind : IntErrorKind }` — a thin struct over the discriminant
    // enum → single-`.mk` record `Trust.Adt.core_num_ParseIntError` whose sole field
    // grounds over the NESTED FAITHFUL 5-constructor `IntErrorKind` inductive (registered
    // post-order by `collect_adt_carriers_recursive`), NOT a `Prod`-flattened union — the
    // record + the nested sum type are both admitted by the modulo-3 axiom gate.
    c.push((
        "parse_int_error",
        "core::num::ParseIntError { kind : IntErrorKind }",
        Ty::adt(
            "core::num::ParseIntError",
            vec![(
                "kind".into(),
                Ty::adt_enum(
                    "core::num::IntErrorKind",
                    vec![
                        VariantDef { name: "Empty".into(), discriminant: 0, fields: vec![] },
                        VariantDef { name: "InvalidDigit".into(), discriminant: 1, fields: vec![] },
                        VariantDef { name: "PosOverflow".into(), discriminant: 2, fields: vec![] },
                        VariantDef { name: "NegOverflow".into(), discriminant: 3, fields: vec![] },
                        VariantDef { name: "Zero".into(), discriminant: 4, fields: vec![] },
                    ],
                ),
            )],
        ),
    ));
    // `Utf8Error { valid_up_to : usize, error_len : Option<u8> }` — a scalar/option
    // struct → single-`.mk` record `Trust.Adt.core_str_Utf8Error` whose `error_len` field
    // grounds over the NESTED FAITHFUL `Option` sum-type inductive (a 2-constructor
    // `None`/`Some(u8)` inductive, registered post-order), NOT the pre-fix flattening that
    // conflated `Option<u8>` with `struct Wrap(u8)`. The record + the nested `Option`
    // inductive are both admitted by the modulo-3 axiom gate.
    c.push((
        "utf8_error",
        "core::str::Utf8Error { valid_up_to : usize, error_len : Option<u8> }",
        Ty::adt(
            "core::str::Utf8Error",
            vec![
                ("valid_up_to".into(), Ty::Int { width: 64, signed: false }),
                (
                    "error_len".into(),
                    Ty::adt_enum(
                        "core::option::Option",
                        vec![
                            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                            VariantDef { name: "Some".into(), discriminant: 1, fields: vec![("0".into(), u8_ty())] },
                        ],
                    ),
                ),
            ],
        ),
    ));

    // --- std containers ---
    c.push(("vec", "Vec<i32>", container_adt("alloc::vec::Vec", i32_ty())));
    c.push(("vecdeque", "VecDeque<i32>", container_adt("alloc::collections::VecDeque", i32_ty())));
    c.push(("string", "String", {
        // String is morally Vec<u8>; its buffer carries the u8 element.
        container_adt("alloc::string::String", u8_ty())
    }));
    c.push(("box", "Box<i32>", smart_ptr_adt("alloc::boxed::Box", i32_ty())));
    c.push(("rc", "Rc<i32>", smart_ptr_adt("alloc::rc::Rc", i32_ty())));
    c.push(("arc", "Arc<i32>", smart_ptr_adt("alloc::sync::Arc", i32_ty())));

    // --- REAL-CODE COVERAGE: COLLECTIONS (maps) → association-list carriers ---
    // A `HashMap<K,V>`/`BTreeMap<K,V>` models as the association-list carrier
    // `Slice (Prod (R K) (R V))` over its recovered `(K, V)` entry tuple. (`String`
    // above already models as `Slice u8` — the Char-list carrier; `VecDeque` above
    // already models as `Slice` like `Vec`.)
    c.push((
        "hashmap",
        "HashMap<u32, i32>  (Slice (Prod u32 i32))",
        map_adt("std::collections::HashMap", u32_ty(), i32_ty()),
    ));
    c.push((
        "btreemap",
        "BTreeMap<u32, i32>  (Slice (Prod u32 i32))",
        map_adt("std::collections::BTreeMap", u32_ty(), i32_ty()),
    ));
    // REAL-CODE COVERAGE — the `HashMap::entry` API (`m.entry(k).or_insert(v)`, the
    // residual-46 `Entry`/`OccupiedEntry`/`VacantEntry`). `Entry<K,V>` IS a 2-variant
    // enum (`Occupied(OccupiedEntry) | Vacant(VacantEntry)`); we model it as a FAITHFUL
    // 2-constructor inductive `Trust.Adt.std_collections_hash_map_Entry` over the (K, V)
    // the entry concerns, where `Occupied` and `Vacant` are DISTINCT constructors (the
    // borrow into the map is a VIEW, not a separately-faithful field). Registered modulo 3
    // (inductive + recursor `axiom_deps` EMPTY — NO 4th axiom); INJECTIVE like any data
    // enum — NOT a `Prod`-flattened union of the variants' fields.
    c.push((
        "hashmap_entry",
        "std::collections::hash_map::Entry<u32, i32>  (Occupied | Vacant)",
        Ty::adt_enum(
            "std::collections::hash_map::Entry",
            vec![
                VariantDef {
                    name: "Occupied".into(),
                    discriminant: 0,
                    fields: vec![("key".into(), u32_ty()), ("value".into(), i32_ty())],
                },
                VariantDef {
                    name: "Vacant".into(),
                    discriminant: 1,
                    fields: vec![("key".into(), u32_ty())],
                },
            ],
        ),
    ));

    // --- REAL-CODE COVERAGE: ITERATOR ADAPTERS → real RECORD carriers ---
    // Each stdlib iterator adapter models as a REAL single-constructor record
    // `Trust.Adt.<Adapter>` over its RECOVERED source + closure/index, NOT the
    // opaque `ptr`/`end_or_len`/`_marker` internal layout.
    // `slice::Iter<i32>` → `{ source : Slice i32 }`.
    c.push((
        "slice_iter",
        "std::slice::Iter<i32>  ({ source : Slice i32 })",
        i32_slice_iter(),
    ));
    // `str::Chars` → `{ source : Slice u8 }` (a `slice::Iter<u8>` wrapper).
    c.push((
        "chars",
        "std::str::Chars  ({ source : Slice u8 })",
        Ty::adt("std::str::Chars", vec![("iter".into(), slice_iter_adt("std::slice::Iter", u8_ty()))]),
    ));
    // `Map<slice::Iter<i32>, {closure}>` → `{ source : <Iter record>, f : <closure> }`.
    c.push((
        "iter_map",
        "Map<slice::Iter<i32>, {closure}>  ({ source, f : closure-record })",
        iter_adapter_adt(
            "std::iter::Map",
            i32_slice_iter(),
            "f",
            Ty::Closure { name: "probe::{closure#0}".into(), upvars: vec![], call: None },
        ),
    ));
    // `Filter<slice::Iter<i32>, {pred}>` → `{ source, pred : <closure> }`.
    c.push((
        "iter_filter",
        "Filter<slice::Iter<i32>, {pred}>  ({ source, pred : closure-record })",
        iter_adapter_adt(
            "std::iter::Filter",
            i32_slice_iter(),
            "predicate",
            Ty::Closure { name: "probe::{closure#1}".into(), upvars: vec![], call: None },
        ),
    ));
    // `Enumerate<slice::Iter<i32>>` → `{ source, pos : usize }`.
    c.push((
        "iter_enumerate",
        "Enumerate<slice::Iter<i32>>  ({ source, pos : usize })",
        Ty::adt(
            "std::iter::Enumerate",
            vec![
                ("iter".into(), i32_slice_iter()),
                ("count".into(), Ty::Int { width: 64, signed: false }),
            ],
        ),
    ));
    // `Zip<slice::Iter<i32>, slice::Iter<i32>>` → `{ a, b }`.
    c.push((
        "iter_zip",
        "Zip<slice::Iter<i32>, slice::Iter<i32>>  ({ a, b })",
        Ty::adt(
            "std::iter::Zip",
            vec![("a".into(), i32_slice_iter()), ("b".into(), i32_slice_iter())],
        ),
    ));
    // `Copied<slice::Iter<i32>>` → TRANSPARENT to its source `slice::Iter` record.
    c.push((
        "iter_copied",
        "Copied<slice::Iter<i32>>  (transparent to source Iter record)",
        Ty::adt("std::iter::Copied", vec![("it".into(), i32_slice_iter())]),
    ));

    // --- REAL-CODE COVERAGE: STRING-PATTERN iterators → real RECORD carriers ---
    // The idiomatic `s.split_whitespace()` / `s.lines()` / `s.char_indices()` /
    // `s.split(p)` iterators were the report's residual-46 opaque adapter ADTs.
    // Each models as a REAL record over its remaining-input byte list (+ needle for
    // a splitter), NOT the opaque `Searcher`/private-field internal layout.
    // `SplitWhitespace` → `{ source : Slice (BitVec 8) }`.
    c.push((
        "split_whitespace",
        "std::str::SplitWhitespace  ({ source : Slice u8 })",
        Ty::adt("std::str::SplitWhitespace", vec![("inner".into(), u8_ty())]),
    ));
    // `Lines` → `{ source : Slice (BitVec 8) }`.
    c.push((
        "str_lines",
        "std::str::Lines  ({ source : Slice u8 })",
        Ty::adt("std::str::Lines", vec![("0".into(), u8_ty())]),
    ));
    // `CharIndices` → `{ source : Slice (BitVec 8) }` (yields `(usize, char)` VIEWS).
    c.push((
        "char_indices",
        "std::str::CharIndices  ({ source : Slice u8 })",
        Ty::adt("std::str::CharIndices", vec![("front_offset".into(), u8_ty())]),
    ));
    // `Split<char>` → `{ source : Slice u8, pattern : Slice u8 }` (the needle).
    c.push((
        "str_split",
        "std::str::Split<char>  ({ source : Slice u8, pattern : Slice u8 })",
        Ty::adt("std::str::Split", vec![("0".into(), u8_ty())]),
    ));
    // `SplitN<char>` → `{ source : Slice u8, pattern : Slice u8 }`.
    c.push((
        "str_splitn",
        "std::str::SplitN<char>  ({ source : Slice u8, pattern : Slice u8 })",
        Ty::adt("std::str::SplitN", vec![("0".into(), u8_ty())]),
    ));
    // Option<i32> / Result<i32,u8> arrive as ENUMS → FAITHFUL 2-constructor inductives
    // `Trust.Adt.core_option_Option` / `Trust.Adt.core_result_Result`. `Some(i32)` ≠
    // `None` (a NULLARY constructor), `Ok(i32)` ≠ `Err(u8)` — DISTINCT constructors with
    // distinct discriminants, registered modulo 3 (inductive + recursor `axiom_deps` EMPTY
    // — NO 4th axiom). The `Option<i32>` carrier `Trust.Adt.core_option_Option` is
    // INJECTIVE: DISTINCT from `struct Wrap(i32)`'s `Prod (BitVec 32) Unit` — NOT the
    // pre-fix non-injective `reflect_struct_product` over the union of variant fields,
    // which conflated Some/None with a 1-field struct.
    c.push((
        "option",
        "Option<i32>",
        Ty::adt_enum(
            "core::option::Option",
            vec![
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "Some".into(), discriminant: 1, fields: vec![("0".into(), i32_ty())] },
            ],
        ),
    ));
    c.push((
        "result",
        "Result<i32, u8>",
        Ty::adt_enum(
            "core::result::Result",
            vec![
                VariantDef { name: "Ok".into(), discriminant: 0, fields: vec![("0".into(), i32_ty())] },
                VariantDef { name: "Err".into(), discriminant: 1, fields: vec![("0".into(), u8_ty())] },
            ],
        ),
    ));
    // generic Option<T> (parameterized enum, not monomorphized)
    c.push((
        "option_generic",
        "Option<T>",
        Ty::adt_enum(
            "core::option::Option",
            vec![
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "Some".into(), discriminant: 1, fields: vec![("0".into(), param("T/#0"))] },
            ],
        ),
    ));

    // --- sequences / tuples ---
    c.push(("array", "[i32; 4]", Ty::Array { elem: Box::new(i32_ty()), len: 4 }));
    c.push(("slice", "&[i32]", Ty::Slice { elem: Box::new(i32_ty()) }));
    c.push((
        "tuple3",
        "(i32, u8, bool)",
        Ty::Tuple(vec![i32_ty(), u8_ty(), Ty::Bool]),
    ));
    // &str — a slice of u8 at the carrier level (str ≈ [u8]).
    c.push(("str", "&str", Ty::Slice { elem: Box::new(u8_ty()) }));

    // --- trait objects / functions / closures ---
    c.push(("dyn_trait", "dyn Trait", Ty::Dynamic { trait_name: "Trait".into() }));
    c.push((
        "fn_ptr",
        "fn(i32) -> u8",
        Ty::FnPtr { sig: Box::new(FnSig { params: vec![i32_ty()], ret: Box::new(u8_ty()) }) },
    ));
    c.push((
        "fn_def",
        "fn item: fn(i32) -> u8",
        Ty::FnDef {
            name: "f".into(),
            sig: Box::new(FnSig { params: vec![i32_ty()], ret: Box::new(u8_ty()) }),
        },
    ));
    // Closures capture upvars; Fn/FnMut/FnOnce all lower to `Ty::Closure` at MIR.
    c.push((
        "closure_fn",
        "impl Fn(i32) -> i32 (captures i32)",
        Ty::Closure { name: "{closure#0}".into(), upvars: vec![i32_ty()], call: None },
    ));
    c.push((
        "closure_fnmut",
        "impl FnMut() (captures u8)",
        Ty::Closure { name: "{closure#1}".into(), upvars: vec![u8_ty()], call: None },
    ));
    c.push((
        "closure_fnonce",
        "impl FnOnce() (captures bool)",
        Ty::Closure { name: "{closure#2}".into(), upvars: vec![Ty::Bool], call: None },
    ));

    // --- associated types / const generics / markers ---
    // An associated type `<T as Trait>::Out` that did not normalize lowers to a
    // generic-param-shaped `TyKind::Param`/projection placeholder.
    c.push(("assoc_type", "<T as Trait>::Out", param("Out/#0")));
    // const generic length parameter `N` appears as a `Ty::Array` len; the generic
    // element `[T; N]` carries the type var element.
    c.push((
        "const_generic_array",
        "[T; N]",
        Ty::Array { elem: Box::new(param("T/#0")), len: 8 },
    ));
    // PhantomData<T> — a zero-field marker struct (no Int content).
    c.push((
        "phantom_data",
        "PhantomData<T>",
        Ty::adt("core::marker::PhantomData", vec![]),
    ));

    // ===================================================================
    // TYPE-ZOO CLOSE (additive) — the six remaining families as REAL Clean
    // dependent types modulo 3. These probes are classified via the family-
    // specific real-kernel grounding gates (`classify_type` dispatch), NOT
    // the existing length-erased / `Trust.Param` fallbacks that the earlier
    // `const_generic_array` / `assoc_type` entries above measure.
    // ===================================================================

    // TYPE-ZOO #1 — CONST GENERICS as a real LENGTH-INDEXED vector: `[i32; 4]`
    // reflects to `Trust.ArrayN Int 4` with `4` a real `Nat` INDEX (the const
    // generic as a dependent value), NOT the length-erased `List`. Distinct from
    // `const_generic_array` above (which measures the erased-element path).
    c.push((
        "const_generic_indexed",
        "[i32; 4] (length-indexed Trust.ArrayN Int 4)",
        Ty::Array { elem: Box::new(i32_ty()), len: 4 },
    ));

    // TYPE-ZOO #2 — impl Trait (RPIT/TAIT): an opaque return type is an
    // EXISTENTIAL `Sigma (T:Type), Vtable T` (the `dyn` analogue under the
    // `Trust.Impl.<trait>` name). Modeled here as a dedicated impl-Trait marker.
    c.push((
        "impl_trait",
        "impl Iterator (RPIT existential)",
        Ty::Dynamic { trait_name: "@impl::core::iter::Iterator".into() },
    ));

    // TYPE-ZOO #3 — MULTI-BOUND trait object `dyn A + B + Send`: a `Sigma` over the
    // CONJOINED vtable record (methods of A AND B; the marker `Send` contributes an
    // empty obligation). A `+`-joined trait_name signals the multi-bound case.
    c.push((
        "dyn_multi_bound",
        "dyn core::fmt::Debug + core::clone::Clone + Send",
        Ty::Dynamic { trait_name: "core::fmt::Debug + core::clone::Clone + Send".into() },
    ));

    // TYPE-ZOO #4 — HRTB `for<'a> Fn(&'a i32) -> bool`: the higher-ranked lifetime
    // quantifier as a real kernel `Pi` over the erased `Trust.Region`, around the fn
    // arrow. Modeled as a fn pointer tagged with a `for<'a>` region count of 1.
    c.push((
        "hrtb_fn",
        "for<'a> fn(&'a i32) -> bool",
        Ty::FnPtr {
            sig: Box::new(FnSig {
                params: vec![Ty::Ref { mutable: false, inner: Box::new(i32_ty()) }],
                ret: Box::new(Ty::Bool),
            }),
        },
    ));

    // TYPE-ZOO #5 — GAT `<T as Iterator>::Item<'a>`: a PARAMETERIZED associated-type
    // FAMILY (a type-level function) `Trust.Gat.Iterator_Item (P:Type) : Type`,
    // indexed by its GAT parameter. Modeled here as a generic-struct-shaped family
    // carrier `Family<P>` whose `Trait::Assoc` name and one `Type` GAT parameter the
    // measurement reflects via `reflect_gat_family`.
    c.push((
        "gat_family",
        "<T as Iterator>::Item<'a> (GAT family)",
        Ty::adt(
            "@gat::core::iter::Iterator::Item",
            vec![("__gat_param".into(), param("P/#0"))],
        ),
    ));

    // TYPE-ZOO #6 — COROUTINE / async state machine: reflects to its state record
    // (`Trust.Coroutine.<name>` — env + resume : S → Y, the suspend-point STATE `S`
    // existentially abstracted as a `Type` param), distinct from the closure record.
    c.push((
        "coroutine",
        "async {} / coroutine (state machine)",
        Ty::Coroutine { name: "{coroutine#0}".into(), upvars: vec![i32_ty()] },
    ));

    c
}

// ===================================================================
// EXPANDED TRUST TYPES corpus — the verification types Trust adds BEYOND Rust
// (the dependent / refinement / spec types), reflected as REAL Clean DEPENDENT
// types modulo 3. These are NOT `Ty` constructors (the Rust ADTs above are
// already covered by `reflect_ty`); each entry reflects through the dedicated
// verification-type entry point (`reflect_refinement` / `reflect_invariant_type`
// / `reflect_spec_function`) and is classified by GROUNDING the carrier in the
// REAL clean-kernel prelude (`ground_verification_type`) and confirming its
// transitive `axiom_deps` is EMPTY (⊆ the 3 — NO 4th axiom). The refinement
// subset reuses the prelude `Subtype` (a dependent SUBSET type already grounded
// modulo 3); the spec'd function is a kernel `Π … → Subtype …`.
// ===================================================================

/// One EXPANDED-TRUST-TYPE corpus probe: a human name + the source spelling +
/// the reflected carrier (built from the dedicated verification-type entry
/// point). `carrier` is `Err` only if the probe is DELIBERATELY fail-closed (a
/// refinement over a non-reflectable / opaque base — the quantified Σ beats an
/// opaque free const), which the measurement records as a FAIL-CLOSED verdict.
pub(crate) struct VerificationTypeProbe {
    pub name: &'static str,
    pub source: &'static str,
    pub carrier: Result<ProofTerm, ReflectError>,
}

/// A `> 0` predicate over `var` (the canonical "positive" refinement `{v | v > 0}`).
fn pred_gt0(var: &str) -> Formula {
    Formula::Gt(Box::new(Formula::Var(var.to_string(), Sort::Int)), Box::new(Formula::Int(0)))
}

/// The EXPANDED-TRUST-TYPE corpus. Each probe reflects a Trust verification type
/// (refinement / invariant-carrying / spec'd-dependent-function) to its Clean
/// dependent carrier via the dedicated `reflect_*` entry point.
pub(crate) fn verification_type_corpus() -> Vec<VerificationTypeProbe> {
    let mut c: Vec<VerificationTypeProbe> = Vec::new();

    // --- REFINEMENT / LIQUID type `{v : T | φ}` → Σ(v:R T), Proof(φ v) = Subtype ---

    // `{v : i32 | v > 0}` — the canonical positive-integer refinement. Grounds to
    // `Subtype Int (λ v. Int.lt 0 v)` (the prelude dependent subset, modulo 3).
    c.push(VerificationTypeProbe {
        name: "refine_pos_i32",
        source: "{v: i32 | v > 0}  (#[refine(\"v > 0\")])",
        carrier: reflect_refinement("v", &i32_ty(), &pred_gt0("v")),
    });

    // `{v : u8 | v < 128}` — a bounded-byte refinement (the ASCII range). Grounds to
    // `Subtype Int (λ v. Int.lt v 128)` (u8 binds at the integer universe).
    c.push(VerificationTypeProbe {
        name: "refine_bounded_u8",
        source: "{v: u8 | v < 128}  (#[refine(\"v < 128\")])",
        carrier: reflect_refinement(
            "v",
            &u8_ty(),
            &Formula::Lt(Box::new(Formula::Var("v".into(), Sort::Int)), Box::new(Formula::Int(128))),
        ),
    });

    // `{v : bool | v}` — a refinement over a NON-integer base (Bool). The predicate
    // `v` (a bare boolean asserted true) grounds via `Trust.Prop.BoolTrue`, and the
    // base binds at `El (Trust.Sort.Bool)` ≡ `Bool` — a refinement over a concrete
    // non-integer carrier, still the prelude `Subtype`.
    c.push(VerificationTypeProbe {
        name: "refine_bool_true",
        source: "{v: bool | v}  (#[refine(\"v\")])",
        carrier: reflect_refinement("v", &Ty::Bool, &Formula::Var("v".into(), Sort::Bool)),
    });

    // --- TYPE INVARIANT `#[invariant(\"φ\")]` → the SAME refinement subset carrier ---

    // A value with `#[invariant("v >= 0")]` is the refinement `{v : i32 | v >= 0}`.
    // Reflected via the dedicated `reflect_invariant_type` entry (records the
    // `#[invariant]` provenance); the carrier IS a `Subtype`, modulo 3.
    c.push(VerificationTypeProbe {
        name: "invariant_nonneg_i32",
        source: "i32 with #[invariant(\"v >= 0\")]  ({v: i32 | v >= 0})",
        carrier: reflect_invariant_type(
            "v",
            &i32_ty(),
            &Formula::Ge(Box::new(Formula::Var("v".into(), Sort::Int)), Box::new(Formula::Int(0))),
        ),
    });

    // --- SPEC'd dependent FUNCTION `fn(x:T) requires{pre} -> {r:U | post}` ---

    // `fn inc(x: i32) requires{x > 0} -> {r: i32 | r > x}` — the dependent function
    // type carrying its contract: `Π(x:Int), Proof(0 < x) → Σ(r:Int), Proof(x < r)`.
    // Grounds to a kernel `Pi` whose codomain is the prelude `Subtype` (modulo 3).
    c.push(VerificationTypeProbe {
        name: "spec_fn_inc",
        source: "fn(x: i32) requires{x > 0} -> {r: i32 | r > x}",
        carrier: reflect_spec_function(
            "x",
            &i32_ty(),
            &pred_gt0("x"),
            "r",
            &i32_ty(),
            &Formula::Gt(
                Box::new(Formula::Var("r".into(), Sort::Int)),
                Box::new(Formula::Var("x".into(), Sort::Int)),
            ),
        ),
    });

    // `fn id_nonneg(x: u8) requires{true} -> {r: u8 | r >= 0}` — a total spec'd
    // function with a trivial precondition and a vacuous-but-real postcondition.
    c.push(VerificationTypeProbe {
        name: "spec_fn_total",
        source: "fn(x: u8) requires{true} -> {r: u8 | r >= 0}",
        carrier: reflect_spec_function(
            "x",
            &u8_ty(),
            &Formula::Bool(true),
            "r",
            &u8_ty(),
            &Formula::Ge(Box::new(Formula::Var("r".into(), Sort::Int)), Box::new(Formula::Int(0))),
        ),
    });

    // --- FAIL-CLOSED control: a refinement over an UNINHABITABLE opaque base ---

    // `{v : ! | v > 0}` — a refinement over the NEVER type. `reflect_ty(!)` fails
    // closed, so `reflect_refinement` fails closed: a refinement needs a real witness
    // carrier, and `!` has none. A quantified Σ over a real carrier beats an opaque
    // free const, so this is recorded as a SOUND fail-closed (NOT structural).
    c.push(VerificationTypeProbe {
        name: "refine_never_fail_closed",
        source: "{v: ! | v > 0}  (NO witness carrier — fails closed)",
        carrier: reflect_refinement("v", &Ty::Never, &pred_gt0("v")),
    });

    c
}
