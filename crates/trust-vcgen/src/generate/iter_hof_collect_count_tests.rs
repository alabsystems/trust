// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Trust (W4 ITER-HOF (c), 2026-09-25): the bounded-source `collect` walk's
//! four widenings, each with the control that must keep the row.
//!
//!  * a fn-ITEM turbofish (`map::<String, for<'_> fn(&'_ str) -> String {ident}>`)
//!    no longer defeats the std-adaptor authenticator (`vc_strip_generics` read
//!    the arrow's `>` as a bracket);
//!  * `BTreeMap::range`/`range_mut`, `BTreeSet::range` are keyed LEAF producers;
//!  * `char::to_lowercase`/`to_uppercase` are keyed CONSTANT-bounded leaves;
//!  * `flat_map` whose buffered `U::IntoIter` is the case-mapping iterator steps
//!    through to its source;
//!
//! and one NARROWING found by the self-check: a leaf whose receiver's elements
//! are zero-sized on their face (`vec![(); n]`) is no longer a bounded source.
//!
//! Every callee spelling and type name is VERBATIM from `-Ztrust-dump=mir` on
//! the stage-1 compiler of this branch's base (`fm1.rs`, `m3.rs`, unaimed-90
//! d1/p11); the bundles are assembled from them. Every test drives the production
//! entry point `generate_unbounded_allocation_vcs`.
//!
//! The trailing `::<__trust_elem_bytes@N>` of every `collect` callee was
//! RE-MEASURED (W4 ITER-HOF fix round 4, 2026-10-02) on the fix-2 stage 1
//! (`011f26cf15`, a merge of main `123f22d176`) and on a stage 1 of main
//! `a3be88bbde`: both render `String` as `@1`, `Vec<u8>` as `@1`, `Vec<&str>` as
//! `@16` and `Vec<String>` as `@24`. Main's W4 HASHMAP r2 (`94df15426d`) made `N`
//! the DESTINATION's element size (it used to be the iterator's own: `@96` is the
//! `FlatMap`, `@120` the `Chain`), and W4 HASHMAP r3's `bounded_source_fits_sink`
//! charges `N` per item a bounded source may yield. The stale `@96`/`@120` made a
//! case-mapping fanout (3 x a `str` view) "overflow" its destination, so three of
//! these tests were red on every merge of that main (fix-2 and fix-3a); see
//! `flat_map_over_a_case_mapping_steps_through_to_its_bounded_source`'s width
//! control for the interaction itself.

use trust_types::live_source_bound::contiguous_capacity_fits;
use trust_types::{
    BasicBlock, CalleeKey, LocalDecl, SysrootItem, UnwindEdge, VariantDef, VerifiableBody,
};

use super::*;

const CHARS_CTOR: &str = "core::str::<impl str>::chars";
const CHARS_NEXT: &str =
    "<core::str::iter::Chars<'_> as core::iter::traits::iterator::Iterator>::next";
const FLAT_MAP_LOWER: &str = "<core::str::iter::Chars<'_> as core::iter::traits::iterator::Iterator>\
     ::flat_map::<core::char::ToLowercase, {closure@fm1.rs:2:24: 2:27}>";
const COLLECT_FLAT_MAP_HEAD: &str = "<core::iter::adapters::flatten::FlatMap<core::str::iter::Chars<'_>, \
     core::char::ToLowercase, {closure@fm1.rs:2:24: 2:27}> as core::iter::traits::iterator::Iterator>\
     ::collect::<alloc::string::String>";

/// The `collect::<String>` callee with a destination element of `elem_bytes`
/// bytes. The extractor renders `String` as `@1`; any other width is a control.
fn collect_flat_map(elem_bytes: u64) -> String {
    format!("{COLLECT_FLAT_MAP_HEAD}{}", trust_types::render_trailing_elem_bytes_token(elem_bytes))
}

fn key(item: Option<SysrootItem>, krate: &str) -> Option<CalleeKey> {
    Some(CalleeKey {
        sysroot_item: item,
        krate_is_real_sysroot: true,
        krate_name_is_ambiguous: false,
        stable_crate_id: 0x1973_d11b_2baa_21fa,
        krate_name: krate.to_string(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    })
}

fn call(
    callee: &str,
    args: Vec<Operand>,
    dest: usize,
    target: Option<BlockId>,
    callee_key: Option<CalleeKey>,
) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target,
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key,
        is_foreign: false,
    }
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn func(locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>, arg_count: usize) -> VerifiableFunction {
    let return_ty = locals[0].ty.clone();
    VerifiableFunction {
        name: "probe".to_string(),
        def_path: "user::probe".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn local(index: usize, ty: Ty) -> LocalDecl {
    LocalDecl { index, ty, name: None }
}

fn str_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) }
}

fn option_of(payload: Ty) -> Ty {
    Ty::adt("core::option::Option", vec![("__tag".into(), Ty::u8()), ("__v1_0".into(), payload)])
}

fn chars_ty() -> Ty {
    Ty::adt("core::str::iter::Chars", vec![])
}

/// `FlatMap<Chars, U, F>` as the extractor renders it, with `buffer` as the
/// `U::IntoIter` held in both `frontiter` and `backiter`.
fn flat_map_ty(buffer: Ty) -> Ty {
    let map = Ty::adt("core::iter::adapters::map::Map", vec![("iter".into(), chars_ty())]);
    let fuse = Ty::adt("core::iter::adapters::fuse::Fuse", vec![("iter".into(), option_of(map))]);
    let compat = Ty::adt(
        "core::iter::adapters::flatten::FlattenCompat",
        vec![
            ("iter".into(), fuse),
            ("frontiter".into(), option_of(buffer.clone())),
            ("backiter".into(), option_of(buffer)),
        ],
    );
    Ty::adt("core::iter::adapters::flatten::FlatMap", vec![("inner".into(), compat)])
}

fn lower() -> Ty {
    Ty::adt("core::char::ToLowercase", vec![])
}

fn rows(f: &VerifiableFunction) -> usize {
    generate_unbounded_allocation_vcs_on_64_bit(f)
        .iter()
        .filter(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } => kind.contains("UnboundedAllocation"),
            other => format!("{other:?}").contains("UnboundedAllocation"),
        })
        .count()
}

/// The `kind` of every `UnsupportedMir` allocation row (the rows [`rows`] counts
/// that carry one), in emission order.
fn unsupported_row_kinds(f: &VerifiableFunction) -> Vec<String> {
    generate_unbounded_allocation_vcs_on_64_bit(f)
        .iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } if kind.contains("UnboundedAllocation") => {
                Some(kind.clone())
            }
            _ => None,
        })
        .collect()
}

/// `s.chars().flat_map(|c| c.to_lowercase()).collect::<String>()`.
fn flat_map_bundle(buffer: Ty, flat_map_key: Option<CalleeKey>) -> VerifiableFunction {
    flat_map_bundle_into(buffer, flat_map_key, 1)
}

/// [`flat_map_bundle`] collecting into a destination whose element is
/// `dest_elem_bytes` bytes (the extractor renders `String` as 1).
fn flat_map_bundle_into(
    buffer: Ty,
    flat_map_key: Option<CalleeKey>,
    dest_elem_bytes: u64,
) -> VerifiableFunction {
    func(
        vec![
            local(0, Ty::adt("alloc::string::String", vec![])),
            local(1, str_ref()),
            local(2, flat_map_ty(buffer)),
            local(3, chars_ty()),
        ],
        vec![
            block(
                0,
                vec![],
                call(
                    CHARS_CTOR,
                    vec![Operand::Copy(Place::local(1))],
                    3,
                    Some(BlockId(1)),
                    key(None, "core"),
                ),
            ),
            block(
                1,
                vec![],
                call(
                    FLAT_MAP_LOWER,
                    vec![Operand::Move(Place::local(3)), Operand::Constant(ConstValue::Int(0))],
                    2,
                    Some(BlockId(2)),
                    flat_map_key,
                ),
            ),
            block(
                2,
                vec![],
                call(
                    &collect_flat_map(dest_elem_bytes),
                    vec![Operand::Move(Place::local(2))],
                    0,
                    None,
                    key(None, "core"),
                ),
            ),
        ],
        1,
    )
}

#[test]
fn flat_map_over_a_case_mapping_steps_through_to_its_bounded_source() {
    assert_eq!(rows(&flat_map_bundle(lower(), key(None, "core"))), 0);
    // `ToUppercase` is the same three-char buffer.
    assert_eq!(
        rows(&flat_map_bundle(Ty::adt("core::char::ToUppercase", vec![]), key(None, "core"))),
        0
    );
    // The grant is a BOUND — three items per item of the `str` view — and main's
    // `bounded_source_fits_sink` charges it against the destination's element. A
    // 64-byte element can hold one item per item of the view but not three of
    // them (the premise), so the fanout keeps a visible row there (the charge).
    let view = LiveSourceCount::str_view().max_items();
    assert!(contiguous_capacity_fits(64, view));
    assert!(!contiguous_capacity_fits(64, view * 3));
    assert_eq!(
        unsupported_row_kinds(&flat_map_bundle_into(lower(), key(None, "core"), 64)),
        vec!["UnboundedAllocation::Iterator::collect::bounded-source-destination-may-overflow"]
    );
}

#[test]
fn flat_map_with_an_unbounded_or_unauthenticated_fanout_keeps_the_row() {
    // `v.iter().flat_map(|&n| 0..n)`: a `Range` per item is not a constant fanout.
    let range = Ty::adt("core::ops::range::Range<u32>", vec![]);
    assert_eq!(rows(&flat_map_bundle(range, key(None, "core"))), 1);
    // An impersonator's `ToLowercase` (stamped) and a user one: no grant.
    let stamped = Ty::adt("__trust_crate@1973d11b2baa21fa::core::char::ToLowercase", vec![]);
    assert_eq!(rows(&flat_map_bundle(stamped, key(None, "core"))), 1);
    let user = Ty::adt("mycrate::char::ToLowercase", vec![]);
    assert_eq!(rows(&flat_map_bundle(user, key(None, "core"))), 1);
    // The adaptor call's DefId is not an artifact-resident sysroot item.
    let mut not_sysroot = key(None, "core");
    if let Some(k) = not_sysroot.as_mut() {
        k.krate_is_real_sysroot = false;
    }
    assert_eq!(rows(&flat_map_bundle(lower(), not_sysroot)), 1);
    // No key at all.
    assert_eq!(rows(&flat_map_bundle(lower(), None)), 1);
}

/// `let mut it = s.chars(); it.next(); it.flat_map(..).collect()`. The `&mut it`
/// conduit that feeds `next` is an `Escape`, which `local_def`'s
/// `has_one_explicit_def` already admits (`body_value_count` counts only whole
/// writes), so this needs no hop of its own — pinned so that stays true for the
/// d0/p06 shape.
fn after_next_bundle() -> VerifiableFunction {
    func(
        vec![
            local(0, Ty::adt("alloc::string::String", vec![])),
            local(1, str_ref()),
            local(2, flat_map_ty(lower())),
            local(3, chars_ty()),
            local(4, Ty::Ref { mutable: true, inner: Box::new(chars_ty()) }),
            local(5, option_of(Ty::u32())),
        ],
        vec![
            block(
                0,
                vec![],
                call(
                    CHARS_CTOR,
                    vec![Operand::Copy(Place::local(1))],
                    3,
                    Some(BlockId(1)),
                    key(None, "core"),
                ),
            ),
            block(
                1,
                vec![Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::Ref { mutable: true, place: Place::local(3) },
                    span: SourceSpan::default(),
                }],
                call(
                    CHARS_NEXT,
                    vec![Operand::Move(Place::local(4))],
                    5,
                    Some(BlockId(2)),
                    key(None, "core"),
                ),
            ),
            block(
                2,
                vec![],
                call(
                    FLAT_MAP_LOWER,
                    vec![Operand::Move(Place::local(3)), Operand::Constant(ConstValue::Int(0))],
                    2,
                    Some(BlockId(3)),
                    key(None, "core"),
                ),
            ),
            block(
                3,
                vec![],
                call(
                    &collect_flat_map(1),
                    vec![Operand::Move(Place::local(2))],
                    0,
                    None,
                    key(None, "core"),
                ),
            ),
        ],
        1,
    )
}

#[test]
fn an_iterator_advanced_by_next_first_is_still_a_bounded_source() {
    assert_eq!(rows(&after_next_bundle()), 0);
}

/// `vec![(); n].iter().map(|_| 1u8).collect::<Vec<u8>>()`, receiver `&[elem]`.
fn slice_map_collect(elem: Ty) -> VerifiableFunction {
    let iter_ty = Ty::adt("core::slice::iter::Iter", vec![]);
    let map_ty = Ty::adt("core::iter::adapters::map::Map", vec![("iter".into(), iter_ty.clone())]);
    func(
        vec![
            local(0, Ty::adt("alloc::vec::Vec<u8>", vec![])),
            local(
                1,
                Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(elem) }) },
            ),
            local(2, map_ty),
            local(3, iter_ty),
        ],
        vec![
            block(
                0,
                vec![],
                call(
                    "core::slice::<impl [()]>::iter",
                    vec![Operand::Copy(Place::local(1))],
                    3,
                    Some(BlockId(1)),
                    key(None, "core"),
                ),
            ),
            block(
                1,
                vec![],
                call(
                    "<core::slice::iter::Iter<'_, ()> as core::iter::traits::iterator::Iterator>::map::<u8, {closure@z.rs:3:18: 3:21}>",
                    vec![Operand::Move(Place::local(3)), Operand::Constant(ConstValue::Int(0))],
                    2,
                    Some(BlockId(2)),
                    key(None, "core"),
                ),
            ),
            block(
                2,
                vec![],
                call(
                    "<core::iter::adapters::map::Map<core::slice::iter::Iter<'_, ()>, {closure@z.rs:3:18: 3:21}> as core::iter::traits::iterator::Iterator>::collect::<alloc::vec::Vec<u8>>::<__trust_elem_bytes@1>",
                    vec![Operand::Move(Place::local(2))],
                    0,
                    None,
                    key(None, "core"),
                ),
            ),
        ],
        1,
    )
}

#[test]
fn a_zero_sized_element_slice_is_not_a_bounded_source() {
    // The control: a sized element keeps the (pre-existing) grant.
    assert_eq!(rows(&slice_map_collect(Ty::u32())), 0);
    // `()`, `PhantomData`/`struct Z;`, `[u64; 0]`, `((), ())`: no allocation bounds
    // the length, so the collect keeps its row.
    assert_eq!(rows(&slice_map_collect(Ty::Unit)), 1);
    assert_eq!(rows(&slice_map_collect(Ty::adt("core::marker::PhantomData", vec![]))), 1);
    assert_eq!(rows(&slice_map_collect(Ty::Array { elem: Box::new(Ty::u32()), len: 0 })), 1);
    assert_eq!(rows(&slice_map_collect(Ty::Tuple(vec![Ty::Unit, Ty::Unit]))), 1);
    // A struct with one sized field is sized.
    assert_eq!(rows(&slice_map_collect(Ty::adt("user::P", vec![("x".into(), Ty::u8())]))), 0);
}

/// An enum as `trust-mir-extract` renders it: the flattened `fields` view (the
/// synthetic `__tag`, then `__v{variant}_{field}`) beside the per-variant view,
/// stamped `AdtKind::Enum` when `stamped` (a hand-built or pre-W19 `Ty::Adt` is not).
fn enum_rendering(name: &str, variants: Vec<(&str, Vec<(String, Ty)>)>, stamped: bool) -> Ty {
    let mut fields = vec![("__tag".to_string(), Ty::Int { width: 64, signed: true })];
    for (vi, (_, vf)) in variants.iter().enumerate() {
        for (fname, fty) in vf {
            fields.push((format!("__v{vi}_{fname}"), fty.clone()));
        }
    }
    Ty::Adt {
        adt_kind: stamped.then_some(trust_types::AdtKind::Enum),
        layout: None,
        name: name.into(),
        fields: fields.into(),
        variants: variants
            .into_iter()
            .enumerate()
            .map(|(i, (n, f))| VariantDef { name: n.into(), discriminant: i as i128, fields: f })
            .collect::<Vec<_>>()
            .into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn option_enum(payload: Ty, stamped: bool) -> Ty {
    enum_rendering(
        "core::option::Option",
        vec![("None", vec![]), ("Some", vec![("0".into(), payload)])],
        stamped,
    )
}

/// W4 ITER-HOF fix round 2 (2026-10-01), adversarial probe p29: a VARIANTLESS enum
/// (`Infallible`) is zero-sized and uninhabited, so `Option<Infallible>` is a ZST
/// (`None` is its only value) and a slice of it bounds no count. Its rendering
/// (one `__tag` field, no variants) used to read as a sized one-field struct.
#[test]
fn a_variantless_enum_payload_is_not_a_bounded_source() {
    for stamped in [true, false] {
        let infallible = enum_rendering("core::convert::Infallible", vec![], stamped);
        assert_eq!(rows(&slice_map_collect(option_enum(infallible.clone(), stamped))), 1);
        assert_eq!(rows(&slice_map_collect(infallible.clone())), 1);
        // A struct around it is no more sized.
        assert_eq!(rows(&slice_map_collect(Ty::adt("user::W", vec![("0".into(), infallible)]))), 1);
        // Controls that keep the grant: a sized payload, and two INHABITED variants
        // (`Option<()>` needs its tag, so it is one byte).
        assert_eq!(rows(&slice_map_collect(option_enum(Ty::u8(), stamped))), 0);
        assert_eq!(rows(&slice_map_collect(option_enum(Ty::Unit, stamped))), 0);
    }
    // An UNSTAMPED enum field view with no variant list (`[__tag, __v1_0]`): the
    // struct arm would read `Option<Infallible>` as sized from `__tag` alone, so it
    // grants nothing — whatever the payload, since no variant can be read from it
    // (fix round 4: fix round 3's exact-`[__tag]` narrowing granted the first).
    let unstamped_infallible = enum_rendering("core::convert::Infallible", vec![], false);
    assert_eq!(rows(&slice_map_collect(option_of(unstamped_infallible))), 1);
    assert_eq!(rows(&slice_map_collect(option_of(Ty::u8()))), 1);
    // A STRUCT whose first field happens to be named `__tag` is still a struct when
    // the extractor stamped it one.
    let tagged_struct = Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        name: "user::Tagged".into(),
        fields: vec![("__tag".into(), Ty::u8())].into(),
        variants: Vec::new().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    assert_eq!(rows(&slice_map_collect(tagged_struct)), 0);
}

/// `c.to_uppercase().collect::<String>()` — the keyed constant leaf.
fn case_mapping_bundle(producer_key: Option<CalleeKey>) -> VerifiableFunction {
    let upper = Ty::adt("core::char::ToUppercase", vec![]);
    func(
        vec![
            local(0, Ty::adt("alloc::string::String", vec![])),
            local(1, Ty::u32()),
            local(2, upper),
        ],
        vec![
            block(
                0,
                vec![],
                call(
                    "core::char::methods::<impl char>::to_uppercase",
                    vec![Operand::Copy(Place::local(1))],
                    2,
                    Some(BlockId(1)),
                    producer_key,
                ),
            ),
            block(
                1,
                vec![],
                call(
                    "<core::char::ToUppercase as core::iter::traits::iterator::Iterator>::collect::<alloc::string::String>::<__trust_elem_bytes@1>",
                    vec![Operand::Move(Place::local(2))],
                    0,
                    None,
                    key(None, "core"),
                ),
            ),
        ],
        1,
    )
}

#[test]
fn a_keyed_case_mapping_is_a_constant_bounded_leaf() {
    assert_eq!(rows(&case_mapping_bundle(key(Some(SysrootItem::CharToUppercase), "core"))), 0);
    // The SAME spelling with no identity, or with another item's identity: no grant.
    assert_eq!(rows(&case_mapping_bundle(key(None, "core"))), 1);
    assert_eq!(rows(&case_mapping_bundle(None)), 1);
    assert_eq!(rows(&case_mapping_bundle(key(Some(SysrootItem::PtrRead), "core"))), 1);
}

/// `c.to_uppercase().chain(chars.flat_map(|c| c.to_lowercase())).collect()` —
/// unaimed-90 d0/p06's `capitalize`, with the `Chain`'s `b` field COMPACTED to a
/// by-name `Datatype` exactly as the extractor renders it (measured,
/// `-Ztrust-dump=mir`: the `FlatMap` subtree exceeds the field budget).
fn chain_bundle(chain_key: Option<CalleeKey>, b_buffer: Ty) -> VerifiableFunction {
    let upper = Ty::adt("core::char::ToUppercase", vec![]);
    let chain_ty = Ty::adt(
        "core::iter::adapters::chain::Chain",
        vec![
            ("a".into(), option_of(upper.clone())),
            ("b".into(), Ty::Datatype { name: "core::option::Option".into(), variants: vec![] }),
        ],
    );
    func(
        vec![
            local(0, Ty::adt("alloc::string::String", vec![])),
            local(1, str_ref()),
            local(2, chain_ty),
            local(3, upper),
            local(4, flat_map_ty(b_buffer)),
            local(5, chars_ty()),
            local(6, Ty::u32()),
        ],
        vec![
            block(
                0,
                vec![],
                call(
                    CHARS_CTOR,
                    vec![Operand::Copy(Place::local(1))],
                    5,
                    Some(BlockId(1)),
                    key(None, "core"),
                ),
            ),
            block(
                1,
                vec![],
                call(
                    "core::char::methods::<impl char>::to_uppercase",
                    vec![Operand::Copy(Place::local(6))],
                    3,
                    Some(BlockId(2)),
                    key(Some(SysrootItem::CharToUppercase), "core"),
                ),
            ),
            block(
                2,
                vec![],
                call(
                    FLAT_MAP_LOWER,
                    vec![Operand::Move(Place::local(5)), Operand::Constant(ConstValue::Int(0))],
                    4,
                    Some(BlockId(3)),
                    key(None, "core"),
                ),
            ),
            block(
                3,
                vec![],
                call(
                    "<core::char::ToUppercase as core::iter::traits::iterator::Iterator>::chain::<core::iter::adapters::flatten::FlatMap<core::str::iter::Chars<'_>, core::char::ToLowercase, {closure@cap.rs:4:66: 4:69}>>",
                    vec![Operand::Move(Place::local(3)), Operand::Move(Place::local(4))],
                    2,
                    Some(BlockId(4)),
                    chain_key,
                ),
            ),
            block(
                4,
                vec![],
                call(
                    "<core::iter::adapters::chain::Chain<core::char::ToUppercase, core::iter::adapters::flatten::FlatMap<core::str::iter::Chars<'_>, core::char::ToLowercase, {closure@cap.rs:4:66: 4:69}>> as core::iter::traits::iterator::Iterator>::collect::<alloc::string::String>::<__trust_elem_bytes@1>",
                    vec![Operand::Move(Place::local(2))],
                    0,
                    None,
                    key(None, "core"),
                ),
            ),
        ],
        1,
    )
}

#[test]
fn a_std_chain_with_a_compacted_half_is_established_by_its_arguments() {
    assert_eq!(rows(&chain_bundle(key(None, "core"), lower())), 0);
    // The chain call's DefId is not an artifact-resident sysroot item: the
    // compacted `b` is then an unestablished source again.
    let mut not_sysroot = key(None, "core");
    if let Some(k) = not_sysroot.as_mut() {
        k.krate_is_real_sysroot = false;
    }
    assert_eq!(rows(&chain_bundle(not_sysroot, lower())), 1);
    // The argument walk is what establishes `b`: an unbounded fanout there keeps the row.
    assert_eq!(
        rows(&chain_bundle(key(None, "core"), Ty::adt("core::ops::range::Range<u32>", vec![]))),
        1
    );
}

/// `m.range(r).map(f).collect::<Vec<&str>>()` (unaimed-90 d1/p11).
fn btree_range_bundle(receiver: Ty, range_key: Option<CalleeKey>) -> VerifiableFunction {
    let range_ty =
        Ty::adt("alloc::collections::btree::map::Range<'_, u64, alloc::string::String>", vec![]);
    let map_ty = Ty::adt("core::iter::adapters::map::Map", vec![("iter".into(), range_ty.clone())]);
    func(
        vec![
            local(0, Ty::adt("alloc::vec::Vec<&str>", vec![])),
            local(1, Ty::Ref { mutable: false, inner: Box::new(receiver) }),
            local(2, map_ty),
            local(3, range_ty),
        ],
        vec![
            block(
                0,
                vec![],
                call(
                    "alloc::collections::btree::map::BTreeMap::<u64, alloc::string::String>::range::<u64, core::ops::range::Range<u64>>",
                    vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Int(0))],
                    3,
                    Some(BlockId(1)),
                    range_key,
                ),
            ),
            block(
                1,
                vec![],
                call(
                    "<alloc::collections::btree::map::Range<'_, u64, alloc::string::String> as core::iter::traits::iterator::Iterator>::map::<&str, {closure@p11.rs:22:40: 22:51}>",
                    vec![Operand::Move(Place::local(3)), Operand::Constant(ConstValue::Int(0))],
                    2,
                    Some(BlockId(2)),
                    key(None, "core"),
                ),
            ),
            block(
                2,
                vec![],
                call(
                    "<core::iter::adapters::map::Map<alloc::collections::btree::map::Range<'_, u64, alloc::string::String>, {closure@p11.rs:22:40: 22:51}> as core::iter::traits::iterator::Iterator>::collect::<alloc::vec::Vec<&str>>::<__trust_elem_bytes@16>",
                    vec![Operand::Move(Place::local(2))],
                    0,
                    None,
                    key(None, "core"),
                ),
            ),
        ],
        1,
    )
}

#[test]
fn a_keyed_btree_range_is_a_collection_producer() {
    let map =
        || Ty::adt("alloc::collections::btree::map::BTreeMap<u64, alloc::string::String>", vec![]);
    assert_eq!(rows(&btree_range_bundle(map(), key(Some(SysrootItem::BTreeMapRange), "alloc"))), 0);
    // Without the compiler's identity the rendered spelling buys nothing.
    assert_eq!(rows(&btree_range_bundle(map(), key(None, "alloc"))), 1);
    assert_eq!(rows(&btree_range_bundle(map(), None)), 1);
    // The receiver OPERAND must authenticate too, as for every collection producer.
    let user = Ty::adt("mycrate::collections::BTreeMap", vec![]);
    assert_eq!(rows(&btree_range_bundle(user, key(Some(SysrootItem::BTreeMapRange), "alloc"))), 1);
}

#[test]
fn the_keyed_leaf_names_exactly_its_five_items() {
    let minted = [
        SysrootItem::BTreeMapRange,
        SysrootItem::BTreeMapRangeMut,
        SysrootItem::BTreeSetRange,
        SysrootItem::CharToLowercase,
        SysrootItem::CharToUppercase,
    ];
    for item in trust_types::ALL_SYSROOT_ITEMS {
        assert_eq!(
            key_is_bounded_keyed_producer(key(Some(*item), "core").as_ref()),
            minted.contains(item),
            "{item:?}"
        );
    }
    assert!(!key_is_bounded_keyed_producer(None));
    assert!(!key_is_bounded_keyed_producer(key(None, "alloc").as_ref()));
}

/// `s.split(' ').map(ident).collect::<Vec<String>>()` — a fn ITEM in the turbofish.
#[test]
fn a_fn_item_turbofish_does_not_defeat_the_adaptor_authenticator() {
    let map = "<core::str::iter::Split<'_, char> as core::iter::traits::iterator::Iterator>::map::\
               <alloc::string::String, for<'_> fn(&'_ str) -> alloc::string::String {m3::ident}>";
    assert_eq!(vc_strip_generics(map), "map");
    assert!(vc_callee_is_std_iter_trait_method(map, "Iterator", "map"));
    assert!(is_authenticated_std_len_preserving_adaptor(map, callee_tail(map)));
    // A user trait of the same shape still fails the root anchor.
    let forged = "<core::str::iter::Split<'_, char> as mycrate::iter::Iterator>::map::\
                  <alloc::string::String, for<'_> fn(&'_ str) -> alloc::string::String {m3::ident}>";
    assert!(!vc_callee_is_std_iter_trait_method(forged, "Iterator", "map"));
    // The arrow inside a QUALIFIED self type no longer closes the qualifier early.
    let qualified = "<core::iter::adapters::map::Map<core::str::iter::Split<'_, char>, \
                     for<'_> fn(&'_ str) -> alloc::string::String {m3::ident}> as \
                     core::iter::traits::iterator::Iterator>::filter::<{closure@x.rs:1:1: 1:2}>";
    assert!(vc_callee_is_std_iter_trait_method(qualified, "Iterator", "filter"));

    let split_ty = Ty::adt("core::str::iter::Split", vec![]);
    let map_ty = Ty::adt("core::iter::adapters::map::Map", vec![("iter".into(), split_ty.clone())]);
    let f = func(
        vec![
            local(0, Ty::adt("alloc::vec::Vec<alloc::string::String>", vec![])),
            local(1, str_ref()),
            local(2, map_ty),
            local(3, split_ty),
        ],
        vec![
            block(
                0,
                vec![],
                call(
                    "core::str::<impl str>::split::<char>",
                    vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Int(32))],
                    3,
                    Some(BlockId(1)),
                    key(None, "core"),
                ),
            ),
            block(
                1,
                vec![],
                call(
                    map,
                    vec![Operand::Move(Place::local(3)), Operand::Constant(ConstValue::Int(0))],
                    2,
                    Some(BlockId(2)),
                    key(None, "core"),
                ),
            ),
            block(
                2,
                vec![],
                call(
                    "<core::iter::adapters::map::Map<core::str::iter::Split<'_, char>, for<'_> fn(&'_ str) -> alloc::string::String {m3::ident}> as core::iter::traits::iterator::Iterator>::collect::<alloc::vec::Vec<alloc::string::String>>::<__trust_elem_bytes@24>",
                    vec![Operand::Move(Place::local(2))],
                    0,
                    None,
                    key(None, "core"),
                ),
            ),
        ],
        1,
    );
    assert_eq!(rows(&f), 0);
}

/// `fn f(mut it: Chain<ToUppercase, _>, s: &str, c: bool, ch: char) -> String
///  { if c { it = ch.to_uppercase().chain(s.chars().flat_map(..)); } it.collect() }`
///
/// The chain-typed PARAMETER `it` (`_1`) has ONE definition in `body.blocks` — the
/// keyed std `chain` call in bb4 — and a SECOND, invisible one at ENTRY: whatever
/// iterator the caller passed, which reaches the `collect` on the `c == false` edge.
/// The entry value's type is the same `Chain` with a COMPACTED `b`, which is exactly
/// the value the `built_by_std_chain` exception lets through on the strength of the
/// call's arguments — arguments the entry value never had.
fn param_chain_bundle() -> VerifiableFunction {
    let upper = Ty::adt("core::char::ToUppercase", vec![]);
    let chain_ty = Ty::adt(
        "core::iter::adapters::chain::Chain",
        vec![
            ("a".into(), option_of(upper.clone())),
            ("b".into(), Ty::Datatype { name: "core::option::Option".into(), variants: vec![] }),
        ],
    );
    func(
        vec![
            local(0, Ty::adt("alloc::string::String", vec![])),
            local(1, chain_ty),
            local(2, str_ref()),
            local(3, Ty::Bool),
            local(4, Ty::u32()),
            local(5, upper),
            local(6, flat_map_ty(lower())),
            local(7, chars_ty()),
        ],
        vec![
            block(
                0,
                vec![],
                Terminator::SwitchInt {
                    exhaustive_enum_unreachable: false,
                    discr: Operand::Copy(Place::local(3)),
                    targets: vec![(0, BlockId(5))],
                    otherwise: BlockId(1),
                    span: SourceSpan::default(),
                },
            ),
            block(
                1,
                vec![],
                call(
                    CHARS_CTOR,
                    vec![Operand::Copy(Place::local(2))],
                    7,
                    Some(BlockId(2)),
                    key(None, "core"),
                ),
            ),
            block(
                2,
                vec![],
                call(
                    "core::char::methods::<impl char>::to_uppercase",
                    vec![Operand::Copy(Place::local(4))],
                    5,
                    Some(BlockId(3)),
                    key(Some(SysrootItem::CharToUppercase), "core"),
                ),
            ),
            block(
                3,
                vec![],
                call(
                    FLAT_MAP_LOWER,
                    vec![Operand::Move(Place::local(7)), Operand::Constant(ConstValue::Int(0))],
                    6,
                    Some(BlockId(4)),
                    key(None, "core"),
                ),
            ),
            block(
                4,
                vec![],
                call(
                    "<core::char::ToUppercase as core::iter::traits::iterator::Iterator>::chain::<core::iter::adapters::flatten::FlatMap<core::str::iter::Chars<'_>, core::char::ToLowercase, {closure@cap.rs:4:66: 4:69}>>",
                    vec![Operand::Move(Place::local(5)), Operand::Move(Place::local(6))],
                    1,
                    Some(BlockId(5)),
                    key(None, "core"),
                ),
            ),
            block(
                5,
                vec![],
                call(
                    "<core::iter::adapters::chain::Chain<core::char::ToUppercase, core::iter::adapters::flatten::FlatMap<core::str::iter::Chars<'_>, core::char::ToLowercase, {closure@cap.rs:4:66: 4:69}>> as core::iter::traits::iterator::Iterator>::collect::<alloc::string::String>::<__trust_elem_bytes@1>",
                    vec![Operand::Move(Place::local(1))],
                    0,
                    None,
                    key(None, "core"),
                ),
            ),
        ],
        4,
    )
}

/// The resolver question for `local_def_call_key` (and `local_def` beside it), asked
/// by `tests/local_defs_seam_lint.rs`: CAN THE LOCAL BE A PARAMETER? It can — `_1`
/// above — and the keyed `chain` call is then that parameter's SECOND value. Both
/// resolvers must refuse it (the seam charges the entry definition), so the compacted
/// entry iterator is NOT credited with the chain call's argument-derived count and the
/// `collect` keeps its row. The control is the same keyed call whose destination is a
/// plain temp: there both resolve, and the row is discharged.
#[test]
fn a_parameter_reseated_by_a_keyed_chain_call_does_not_resolve_to_that_call() {
    let param = param_chain_bundle();
    assert!(local_def_call_key(&param, 1).is_none(), "a parameter's body call is its SECOND value");
    assert!(local_def(&param, 1).is_none(), "a parameter's body call is its SECOND value");
    assert_eq!(rows(&param), 1, "the entry iterator must not borrow the chain call's count");

    let temp = chain_bundle(key(None, "core"), lower());
    assert!(local_def_call_key(&temp, 2).is_some_and(|k| k.krate_is_real_sysroot));
    assert!(matches!(local_def(&temp, 2), Some(LocalDef::Call { .. })));
    assert_eq!(rows(&temp), 0);
}

// ── CL-FOLD-LOCALDEF-1 (2026-10-11): `local_def` asks the VALUE question ─────────
//
// Every row below reads a `-Ztrust-dump=mir-only` capture of the stage 1 of
// `2bf0ad72e3` (`scratchpad/stage1-w22probe`, `-Copt-level=0`), committed beside the
// end-to-end rows in `tests/fold_source_value_def_realmir.rs`. Each source is quoted
// in the test that reads it.

fn realmir(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("the captured MIR fixture must deserialize")
}

/// The local the source names `name`.
fn named_local(func: &VerifiableFunction, name: &str) -> usize {
    func.body
        .locals
        .iter()
        .find(|l| l.name.as_deref() == Some(name))
        .map(|l| l.index)
        .unwrap_or_else(|| panic!("{}: no local named `{name}`", func.name))
}

/// The operand handed to the one `Iterator::sum` call.
fn sum_source(func: &VerifiableFunction) -> &Operand {
    func.body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func: callee, args, .. } if callee.contains("::sum::") => {
                args.first()
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("{}: no Iterator::sum call", func.name))
}

/// A range CHANGED after it was built does not resolve to its construction. Each
/// shape's sum row was PROVED, kernel-certified, under certify (or proved under the
/// default policy, for the closures) on the stage 1 of `2bf0ad72e3`, and each panics:
///
///  * `field`: `let mut r = 0u8..4; r.end = 200;` — a projected store (`Partial`);
///  * `param`: `r.end = n` — the same, with a parameter;
///  * `mutref`: `let p = &mut r; p.end = 200;` — a store through an alias (`Escape`);
///  * `fnitem`: `widen(&mut r)` with `fn widen(q: &mut Range<u8>) { q.end = 200 }`;
///  * `swap`: `core::mem::swap(&mut r, &mut big)` with `big = 0u8..200`;
///  * `closure_field`: `let mut g = || r.end = 200; g();`;
///  * `closure_whole`: `let mut g = || r = 0..200; g();`.
///
/// The control `ctl_plain` (`let r = 0u8..4;`, never touched again) resolves.
#[test]
fn a_range_changed_after_construction_does_not_resolve_to_it() {
    for name in [
        "fold_localdef_field",
        "fold_localdef_param",
        "fold_localdef_mutref",
        "fold_localdef_fnitem",
        "fold_localdef_swap",
        "fold_localdef_closure_field",
        "fold_localdef_closure_whole",
    ] {
        let f = realmir(name);
        let r = named_local(&f, "r");
        assert!(local_def(&f, r).is_none(), "{name}: `r` must not resolve to its construction");
        let bound = fold_source_bound(&f, sum_source(&f), 0);
        assert!(
            bound.count.is_none() && bound.items.is_none(),
            "{name}: the sum source must have no bound"
        );
    }
    let f = realmir("fold_localdef_ctl_plain");
    let r = named_local(&f, "r");
    assert!(
        matches!(local_def(&f, r), Some(LocalDef::Rvalue(Rvalue::Aggregate(..)))),
        "an unmodified range resolves to its aggregate"
    );
    let bound = fold_source_bound(&f, sum_source(&f), 0);
    assert!(bound.count.is_some() && bound.items.is_some(), "and bounds its sum");
}

/// The `RangeInclusive::new` CALL-DESTINATION arm, and `local_def_call_key` beside it:
/// `let mut r = 0u8..=3; let p = &mut r; *p = 0..=200; r.sum::<u8>()` (`incl_escape`)
/// and the slice twin `let mut r = 0usize..=0; let p = &mut r; *p = 0..=100;
/// v[r].len()` (`slice_incl_escape`), whose slice row
/// (`collection_range::norm_usize_range`) was PROVED, kernel-certified, under certify.
/// The value `r` holds at the read is `*p`'s, not the call's.
#[test]
fn an_inclusive_range_reseated_through_an_alias_does_not_resolve_to_its_call() {
    for name in ["fold_localdef_incl_escape", "fold_localdef_slice_incl_escape"] {
        let f = realmir(name);
        let r = named_local(&f, "r");
        assert!(local_def(&f, r).is_none(), "{name}: `r` must not resolve to its constructor");
        assert!(local_def_call_key(&f, r).is_none(), "{name}: nor to the constructor's key");
        assert!(
            fold_range_origin(&f, r).is_none(),
            "{name}: the conduit is written through, so the origin gate refuses it too"
        );
    }
}

/// THE PRECISION RECOVERY, admitted: `let mut r = 0u8..4; r.next(); r.sum::<u8>()`
/// (`ctl_next`) and its `RangeInclusive::new` twin (`ctl_next_incl`). The VALUE question
/// refuses `r` (`next` takes `&mut r`); [`fold_range_origin`] answers, because that
/// borrow's only use is argument 0 of core's `Iterator::next`, by its rendered path
/// and its compiler-minted key.
#[test]
fn a_range_whose_only_alias_feeds_core_next_bounds_its_sum_through_the_origin() {
    for name in ["fold_localdef_ctl_next", "fold_localdef_ctl_next_incl"] {
        let f = realmir(name);
        let r = named_local(&f, "r");
        assert!(local_def(&f, r).is_none(), "{name}: the VALUE question refuses the alias");
        assert!(fold_range_origin(&f, r).is_some(), "{name}: the origin gate admits it");
        let bound = fold_source_bound(&f, sum_source(&f), 0);
        assert!(bound.count.is_some() && bound.items.is_some(), "{name}: the sum is bounded");
    }
}

/// THE PRECISION RECOVERY, refused:
///
///  * `next_then_widen`: `r.next(); let p = &mut r; p.end = 200; r.sum::<u8>()` — one
///    conduit feeds `next`, the other is WRITTEN THROUGH;
///  * `ctl_next` with the `next` call's compiler-minted key removed, and with a key
///    whose crate is not the real sysroot — the rendered path alone does not
///    authenticate `next`.
#[test]
fn the_origin_gate_refuses_a_store_through_and_an_unkeyed_next() {
    let f = realmir("fold_localdef_next_then_widen");
    let r = named_local(&f, "r");
    assert!(fold_range_origin(&f, r).is_none(), "a conduit is written through");
    assert!(fold_source_bound(&f, sum_source(&f), 0).count.is_none());

    for real_sysroot in [None, Some(false)] {
        let mut f = realmir("fold_localdef_ctl_next");
        let mut rekeyed = 0;
        for b in &mut f.body.blocks {
            if let Terminator::Call { func: callee, callee_key, .. } = &mut b.terminator
                && callee.ends_with("::next")
            {
                match real_sysroot {
                    None => *callee_key = None,
                    Some(real) => {
                        callee_key
                            .as_mut()
                            .expect("the capture keys `next`")
                            .krate_is_real_sysroot = real;
                    }
                }
                rekeyed += 1;
            }
        }
        assert_eq!(rekeyed, 1, "the capture has one `next` call");
        let r = named_local(&f, "r");
        assert!(
            fold_range_origin(&f, r).is_none(),
            "{real_sysroot:?}: `next` is not core's by key"
        );
        assert!(fold_source_bound(&f, sum_source(&f), 0).count.is_none());
    }
}
