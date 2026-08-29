// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! # "Authenticated sysroot" is not the same property as "bounded"
//!
//! Three rounds (2026-08-16 … 2026-08-17) were spent making the sysroot-provenance
//! authenticators exact. This module is about the sentence that survived all of
//! them: an authenticated crate can hand out a genuine standard-library iterator
//! that never ends.
//!
//! ## The measured refutation
//!
//! ```ignore
//! // aux, PLAIN SAFE RUST, built `--crate-name std` into a `#![no_std]` graph
//! pub struct Vec<T> { pub k: u64, pub t: core::marker::PhantomData<T> }
//! impl<'a, T> IntoIterator for &'a Vec<T> {
//!     type Item = u64;
//!     type IntoIter = core::ops::RangeFrom<u64>;                 // GENUINE `core`
//!     fn into_iter(self) -> Self::IntoIter { core::ops::RangeFrom { start: 0 } }
//! }
//! // consumer
//! pub fn boom(v: &std::vec::Vec<u8>) -> alloc::vec::Vec<u64> { v.into_iter().collect() }
//! ```
//!
//! MEASURED on `stage2/bin/trustc`, `rustc 1.99.0-dev (0a3cd0152 2026-08-17)`:
//! consumer **exit 0 with zero diagnostic lines**; the byte-identical aux renamed
//! `mycrate` is **exit 1 with 49 diagnostic lines**. `RangeFrom::next` never
//! returns `None`, so `boom` allocates without bound in every execution.
//!
//! Every provenance authenticator reads `true` on that bundle and is RIGHT to:
//! `core::ops::range::RangeFrom` really is the real `core`'s ADT and really is
//! correctly unstamped. The defect is that the walk's conclusion —
//! `count <= source.len()` — is a BOUNDEDNESS claim, and no amount of provenance
//! evidence supports it. The fixtures are verbatim compiler output; the sources
//! and the raw compiler transcripts are named in
//! `fixtures/unbounded-sysroot-iterator-2026-08-17/PROVENANCE.md`.
//!
//! ## The two repairs, and what each one alone would leave open
//!
//! * [`ty_is_unbounded_sysroot_iterator`] — the VALUE side. Refuses the sysroot
//!   iterator ADTs that are unbounded on their own account, and looks THROUGH the
//!   rendered field tree, because `core::iter::Map<core::ops::RangeFrom<u64>,
//!   fn(u64) -> u64>` is exactly as endless and exactly as `core`-rooted (also
//!   measured; also a fixture). This half holds even if provenance
//!   authentication fails completely.
//! * [`producer_receiver_value_is_authenticated_sysroot`] — the STRING side. The
//!   extractor's stamp is keyed on the callee's DEFINING crate, so an
//!   impersonator's name reaching the rendered callee only as somebody else's
//!   qualified SELF TYPE is never stamped, and `producer_receiver_path` reads
//!   `std::vec::Vec` straight off the forgery. The receiver OPERAND's `Ty` IS
//!   stamped, so this half asks a source the impersonator does not control. It
//!   closes the whole class rather than the individual endless types.

use super::*;
use crate::{LocalDecl, VerifiableBody};

/// The `{:016x}` `StableCrateId` the compiler assigned to the aux built
/// `--crate-name std` (decimal 1127107163555717956, MEASURED with `trustc
/// -Zls=all`) — the value the patched type-name renderer writes into the stamp.
const IMPERSONATOR_STAMP: &str = "__trust_crate@0fa449fe5b896344::";

const RANGEFROM_EXPLOIT: &str = include_str!("../../fixtures/refute3-rangefrom/exploit.json");
const MAP_EXPLOIT: &str = include_str!(
    "../../fixtures/unbounded-sysroot-iterator-2026-08-17/map_over_rangefrom_impersonating_std.json"
);
const MAP_CONTROL: &str = include_str!(
    "../../fixtures/unbounded-sysroot-iterator-2026-08-17/map_over_rangefrom_ordinary_crate_name.json"
);
const COMPACTED_EXPLOIT: &str = include_str!(
    "../../fixtures/compacted-source-2026-08-18/compacted_cycle_impersonating_std.json"
);
const COMPACTED_CONTROL: &str = include_str!(
    "../../fixtures/compacted-source-2026-08-18/compacted_cycle_ordinary_crate_name.json"
);
const COMPOSED_EXPLOIT: &str = include_str!(
    "../../fixtures/adaptor-over-user-iterator-2026-08-18/map_over_user_iterator_impersonating_std.json"
);
const COMPOSED_CONTROL: &str = include_str!(
    "../../fixtures/adaptor-over-user-iterator-2026-08-18/map_over_user_iterator_ordinary_crate_name.json"
);
const BOUNDED_USER_ELEMENT: &str = include_str!(
    "../../fixtures/adaptor-over-user-iterator-2026-08-18/cloned_slice_of_user_elements_ok.json"
);
const CHAINED_EXPLOIT: &str = include_str!(
    "../../fixtures/adaptor-over-user-iterator-2026-08-18/chain_over_user_iterator_impersonating_std.json"
);
const CHAINED_CONTROL: &str = include_str!(
    "../../fixtures/adaptor-over-user-iterator-2026-08-18/chain_over_user_iterator_ordinary_crate_name.json"
);

fn parse(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).unwrap_or_else(|e| panic!("parse fixture: {e}"))
}

fn unbounded_rows(func: &VerifiableFunction) -> usize {
    generate_unbounded_allocation_vcs(func)
        .iter()
        .filter(|vc| format!("{:?}", vc.kind).contains("UnboundedAllocation"))
        .count()
}

/// The bundle as the PATCHED extractor renders it: the type-name renderer stamps
/// every `Ty::Adt` NAME whose defining crate is the impersonator. In these
/// bundles that is exactly `std::vec::Vec` — `core::ops::range::RangeFrom` and
/// `core::iter::adapters::map::Map` belong to the real `core` and are correctly
/// left bare, which is the entire point of the refutation.
fn with_producer_stamp(json: &str) -> VerifiableFunction {
    let stamped = json.replace(
        "\"name\": \"std::vec::Vec\"",
        &format!("\"name\": \"{IMPERSONATOR_STAMP}std::vec::Vec\""),
    );
    assert!(stamped.contains(IMPERSONATOR_STAMP), "substitution must have applied");
    parse(&stamped)
}

fn adt(name: &str) -> Ty {
    Ty::adt(name, Vec::new())
}

/// The receiver type the compiler actually renders for `producer`'s `self`, for
/// hand-built bundles that used to carry a `Ty::u32()` placeholder there.
///
/// A placeholder was harmless while the receiver's provenance was read only out of
/// the callee STRING; it is not harmless now that
/// [`producer_receiver_value_is_authenticated_sysroot`] reads the operand's own
/// type, and a bundle no compiler could emit would have made those tests silently
/// stop exercising their own subject. The three shapes here are the three MEASURED
/// at the grant sites of the 2 572-bundle corpus: `&[T]` for the slice inherent
/// producers, `&str` for the str views, and `&Collection` for everything else.
pub(super) fn faithful_receiver_ty(producer: &str) -> Ty {
    let recv = producer_receiver_path(producer);
    let inner = if recv.starts_with("core::slice") || recv.starts_with("std::slice") {
        Ty::Slice { elem: Box::new(Ty::u32()) }
    } else if recv.starts_with("core::str")
        || recv.starts_with("alloc::string")
        || recv.starts_with("std::string")
    {
        Ty::Str
    } else {
        adt(&recv)
    };
    Ty::Ref { mutable: false, inner: Box::new(inner) }
}

// ======================================================================
// 1. The VALUE side: which sysroot iterator ADTs are unbounded
// ======================================================================

/// FALSIFY-ONCE for the deny-list itself. The planted violation is asserted FIRST
/// and it is the exact defect: every name below PASSES the provenance
/// authenticator, so before this list existed the walk had nothing left to refuse
/// them with.
#[test]
fn the_genuinely_unbounded_sysroot_iterators_are_refused_by_name() {
    const UNBOUNDED: &[&str] = &[
        // the range family
        "core::ops::range::RangeFrom",
        "core::ops::range::RangeFrom<u64>",
        "core::ops::RangeFrom",
        "std::ops::range::RangeFrom",
        // `core::iter::sources`, defining-module spelling
        "core::iter::sources::repeat::Repeat<u8>",
        "core::iter::sources::repeat_with::RepeatWith<fn() -> u8>",
        "core::iter::sources::successors::Successors<u64, fn(&u64) -> Option<u64>>",
        "core::iter::sources::from_fn::FromFn<fn() -> Option<u8>>",
        "core::iter::sources::from_coroutine::FromCoroutine<C>",
        // …and the re-export spelling, both crates
        "core::iter::Repeat<u8>",
        "std::iter::RepeatWith<F>",
        "std::iter::Successors<T, F>",
        // the adaptor that manufactures infinity from a finite source
        "core::iter::adapters::cycle::Cycle<core::slice::iter::Iter<'_, u8>>",
        "std::iter::Cycle<I>",
    ];
    for name in UNBOUNDED {
        assert!(
            ty_is_authenticated_std_iterator(&adt(name)),
            "planted violation is gone: `{name}` no longer passes the PROVENANCE \
             authenticator, so refusing it here would prove nothing about boundedness"
        );
        assert!(
            unbounded_sysroot_iterator_adt_name(name).is_some(),
            "a genuinely unbounded sysroot iterator must be refused by name: {name}"
        );
        assert!(ty_is_unbounded_sysroot_iterator(&adt(name)), "{name}");
    }

    // The other side of the ledger — refusing these would be an over-decline, and
    // each is finite by construction: `Empty` yields 0, `Once`/`OnceWith` yield 1,
    // `RepeatN` yields its `n`. The bounded collection iterators must be untouched.
    const NOT_REFUSED: &[&str] = &[
        "core::iter::sources::empty::Empty<u8>",
        "core::iter::sources::once::Once<u8>",
        "core::iter::sources::once_with::OnceWith<F>",
        "core::iter::sources::repeat_n::RepeatN<u8>",
        "core::iter::Empty<u8>",
        "core::slice::iter::Iter<'_, u8>",
        "alloc::vec::into_iter::IntoIter<u8>",
        "std::collections::hash::map::Keys<'_, K, V>",
        "core::iter::adapters::map::Map<core::slice::iter::Iter<'_, u8>, [closure]>",
        "core::ops::range::Range<u32>",
        "core::ops::range::RangeInclusive<u32>",
        // a USER type whose tail merely reads like one of ours
        "mycrate::iter::Repeat",
        "mycrate::iter::sources::repeat::Repeat",
        "mycrate::ops::range::RangeFrom",
    ];
    for name in NOT_REFUSED {
        assert!(
            unbounded_sysroot_iterator_adt_name(name).is_none(),
            "over-decline: `{name}` is not a known-unbounded sysroot iterator"
        );
        assert!(!ty_is_unbounded_sysroot_iterator(&adt(name)), "{name}");
    }
}

/// The two lanes that decide "is this range finite" must PARTITION the family, so
/// they cannot drift apart the next time it grows. `iter_collect_count` counts
/// `Range`/`RangeInclusive` and declines the rest; the refusal list is written as
/// the complement of that same [`range_family_adt_name`] answer rather than as a
/// second literal list.
#[test]
fn the_range_family_is_partitioned_between_the_two_lanes() {
    const FAMILY: &[(&str, bool)] = &[
        ("core::ops::range::Range<u32>", true),
        ("core::ops::range::RangeInclusive<u32>", true),
        ("core::ops::range::RangeFrom<u32>", false),
        ("core::ops::range::RangeTo<u32>", false),
        ("core::ops::range::RangeFull", false),
    ];
    for (name, counted_by_the_count_lane) in FAMILY {
        let family = range_family_adt_name(name);
        assert!(family.is_some(), "the family anchor must recognize {name}");
        let counted = matches!(family, Some("Range" | "RangeInclusive"));
        assert_eq!(counted, *counted_by_the_count_lane, "{name}");
        assert_eq!(
            unbounded_sysroot_iterator_adt_name(name).is_some(),
            !counted,
            "the bounded-source lane and the count lane disagree about {name}"
        );
    }
}

/// FALSIFY-ONCE for the FIELD walk. The planted violation is that the NAME test —
/// the whole of what the round-3 review asked for — cannot see this one, because
/// generic stripping deletes the argument that carries the infinity.
#[test]
fn the_field_walk_sees_infinity_hidden_in_a_generic_argument() {
    const MAP_OVER_RANGEFROM: &str =
        "core::iter::adapters::map::Map<core::ops::range::RangeFrom<u64>, fn(u64) -> u64>";
    assert!(
        unbounded_sysroot_iterator_adt_name(MAP_OVER_RANGEFROM).is_none(),
        "planted violation is gone: the NAME test now sees this spelling, so the field \
         walk below is no longer what is being measured"
    );
    assert!(
        ty_is_authenticated_std_iterator(&adt(MAP_OVER_RANGEFROM)),
        "planted violation is gone: the provenance authenticator now refuses it"
    );

    // The compiler's own rendering, verbatim from the fixture: `Map`'s `iter`
    // field IS the `RangeFrom`, so the answer was in the bundle all along.
    let value = Ty::adt(
        "core::iter::adapters::map::Map",
        vec![
            (
                "iter".to_string(),
                Ty::adt("core::ops::range::RangeFrom", vec![("start".to_string(), Ty::u64())]),
            ),
            ("f".to_string(), Ty::u64()),
        ],
    );
    assert!(ty_is_unbounded_sysroot_iterator(&value));

    // …and the same shape with a BOUNDED inner iterator is not refused, so this is
    // an anchor and not a blanket ban on `Map`.
    let bounded = Ty::adt(
        "core::iter::adapters::map::Map",
        vec![
            ("iter".to_string(), Ty::adt("core::slice::iter::Iter", vec![])),
            ("f".to_string(), Ty::u64()),
        ],
    );
    assert!(!ty_is_unbounded_sysroot_iterator(&bounded));
}

/// The row differential on the REAL `Map<RangeFrom<u64>, fn(u64) -> u64>` bundles.
/// Verbatim `-Ztrust-dump=mir` output; the aux differs only in `--crate-name`.
#[test]
fn the_map_over_rangefrom_bundles_are_gated_on_both_sides_now() {
    // Non-vacuity: neither bundle carries a stamp as the compiler emitted it.
    assert!(!trust_types::path_has_unauthenticated_crate_stamp(MAP_EXPLOIT));
    // The control was ALWAYS gated — the exploit is one crate name away from it.
    assert_eq!(unbounded_rows(&parse(MAP_CONTROL)), 1, "control must be gated");
    // The exploit is gated now, verbatim AND with the producer's type-name stamp.
    assert_eq!(unbounded_rows(&parse(MAP_EXPLOIT)), 1, "verbatim exploit");
    assert_eq!(unbounded_rows(&with_producer_stamp(MAP_EXPLOIT)), 1, "stamped exploit");
}

/// The iterator local of a `v.into_iter().collect()` / `v.iter()…collect()`
/// bundle: the operand the collect sink reads. Read out of the bundle rather
/// than hand-built, so a test asserting things about it is asserting things
/// about what the compiler actually rendered.
fn collected_operand_ty(func: &VerifiableFunction) -> &Ty {
    let op = func
        .body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func: callee, args, .. } if is_collect_sink(callee) => args.first(),
            _ => None,
        })
        .expect("the collect sink");
    let local = operand_local(op).expect("an unprojected iterator local");
    crate::local_ty_ref(func, local).expect("the iterator local's type")
}

// ======================================================================
// 1b. The value side when the value is NOT FULLY RENDERED (2026-08-18)
// ======================================================================

/// FALSIFY-ONCE for the compacted source. The planted violations are asserted
/// FIRST and they are the whole defect: on the value the compiler actually
/// rendered, BOTH pre-existing value-side tests grant, because the extractor
/// deleted the subtree that carried the infinity before either of them ran.
#[test]
fn the_compacted_source_is_refused_under_a_sysroot_iterator_root() {
    let exploit = parse(COMPACTED_EXPLOIT);
    let value = collected_operand_ty(&exploit);

    // Non-vacuity: this really is the erasure, not a hand-built shape. The whole
    // `StepBy<Skip<Peekable<Enumerate<Cycle<Range<u64>>>>>>` subtree is one
    // marker whose surviving name is `core::option::Option`.
    let Ty::Adt { name: root, fields, .. } = value else { panic!("{value:?}") };
    assert_eq!(root, "core::iter::adapters::fuse::Fuse");
    assert_eq!(fields.len(), 1);
    assert!(
        matches!(&fields[0].1, Ty::Datatype { name, variants }
                 if name == "core::option::Option" && variants.is_empty()),
        "the compacted marker: {:?}",
        fields[0].1
    );

    // PLANTED VIOLATION 1: the deny-list cannot see it. Neither the root nor the
    // only name that survived compaction is a known-unbounded sysroot iterator,
    // and neither could ever be — `Option` is not an iterator at all.
    assert!(unbounded_sysroot_iterator_adt_name(root).is_none());
    assert!(unbounded_sysroot_iterator_adt_name("core::option::Option").is_none());
    // PLANTED VIOLATION 2: the provenance authenticator grants, and is right to —
    // `Fuse` is genuine `core`.
    assert!(
        ty_is_authenticated_std_iterator(value),
        "planted violation is gone: the provenance half now refuses this value, so the \
         boundedness refusal below is no longer what is being measured"
    );

    // The refusal.
    assert!(ty_is_unbounded_sysroot_iterator(value));

    // …and the row differential on the real bundles, through the production
    // entry point. The two programs differ only in the aux crate's name and both
    // allocate without bound in every execution.
    assert_eq!(unbounded_rows(&parse(COMPACTED_CONTROL)), 1, "control must be gated");
    assert_eq!(unbounded_rows(&exploit), 1, "the compacted exploit is gated now");
}

/// FALSIFY-ONCE for the composed source. The planted violations are the two
/// value-side conjuncts and the receiver conjunct: all three grant this bundle,
/// so nothing that already existed was going to refuse it.
#[test]
fn a_sysroot_adaptor_over_an_unauthenticated_source_is_refused() {
    let exploit = parse(COMPOSED_EXPLOIT);
    let value = collected_operand_ty(&exploit);

    // Non-vacuity: the compiler rendered the adapted source in full, and it
    // belongs to an ordinary third crate — NOT to the impersonator, which is the
    // half a name test could never decide (see the fixture's PROVENANCE).
    let Ty::Adt { name: root, fields, .. } = value else { panic!("{value:?}") };
    assert_eq!(root, "core::iter::adapters::map::Map");
    assert!(
        matches!(&fields[0].1, Ty::Adt { name, .. } if name == "endcrate::Endless"),
        "the adapted source: {:?}",
        fields[0].1
    );

    // PLANTED VIOLATION 1: provenance grants. It is a ROOT test by design, and
    // the root is genuine `core`.
    assert!(ty_is_authenticated_std_iterator(value));
    // PLANTED VIOLATION 2: the deny-list has nothing to match. It is a list of
    // SYSROOT names and the endless type is not one.
    assert!(unbounded_sysroot_iterator_adt_name(root).is_none());
    assert!(unbounded_sysroot_iterator_adt_name("endcrate::Endless").is_none());
    // PLANTED VIOLATION 3: the receiver conjunct grants too — the forged receiver
    // reaches the bundle unstamped, so the string side is not what closes this.
    let (_, args) = exploit
        .body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func, args, .. } if callee_tail(func) == "into_iter" => {
                Some((func.clone(), args.clone()))
            }
            _ => None,
        })
        .expect("the `into_iter` producer call");
    assert!(
        producer_receiver_value_is_authenticated_sysroot(&exploit, &args),
        "planted violation is gone: the receiver conjunct now refuses this bundle, so the \
         value-side refusal below is no longer what is being measured"
    );

    // The refusal.
    assert!(ty_is_unbounded_sysroot_iterator(value));

    assert_eq!(unbounded_rows(&parse(COMPOSED_CONTROL)), 1, "control must be gated");
    assert_eq!(unbounded_rows(&exploit), 1, "the composed exploit is gated now");
}

/// The composed source ONE LEVEL DOWN, inside `core`'s own `Option` — the shape
/// the refusal above still granted while it stopped at the first non-iterator
/// sysroot ADT. FALSIFY-ONCE: the planted violation is that `Option` is a
/// perfectly authenticated sysroot ADT, so a rule that stops at one stops here.
#[test]
fn a_sysroot_adaptor_over_a_source_wrapped_in_option_is_refused() {
    let exploit = parse(CHAINED_EXPLOIT);
    let value = collected_operand_ty(&exploit);

    let Ty::Adt { name: root, fields, .. } = value else { panic!("{value:?}") };
    assert_eq!(root, "core::iter::adapters::chain::Chain");
    // PLANTED VIOLATION: the adapted source is NOT a direct field — the field is
    // `core::option::Option`, which authenticates as sysroot on every test this
    // module has.
    let Ty::Adt { name: wrapper, .. } = &fields[0].1 else { panic!("{:?}", fields[0].1) };
    assert_eq!(wrapper, "core::option::Option");
    assert!(trust_types::path_root_is_authenticated_sysroot_crate(wrapper));
    assert!(unbounded_sysroot_iterator_adt_name(wrapper).is_none());
    // …and the user iterator really is inside it, in both renderings the
    // extractor emits for an enum.
    let rendered = format!("{:?}", fields[0].1);
    assert!(rendered.contains("endcrate::Endless"), "{rendered}");

    assert!(ty_is_unbounded_sysroot_iterator(value));
    assert_eq!(unbounded_rows(&parse(CHAINED_CONTROL)), 1, "control must be gated");
    assert_eq!(unbounded_rows(&exploit), 1, "the chained exploit is gated now");
}

/// THE OVER-DECLINE BOUND, and the reason `adaptor_source_field_unestablished`
/// stops at the first non-iterator sysroot ADT instead of walking the whole tree.
///
/// `Cloned<slice::Iter<'_, mycrate::Item>>` carries an unauthenticated ADT too —
/// as the ELEMENT of a sysroot iterator, not as the SOURCE of a sysroot adaptor.
/// This bundle is an ordinary crate with no forgery anywhere; it compiled exit 0
/// with no diagnostics and must keep its grant.
///
/// MEASURED cost of removing the stop (the bound deleted, everything else
/// unchanged): the 2 575 checked-in bundles fall from 8 granted collect sites to
/// 4 and from 23 to 27 unbounded-allocation rows — four real-code grants lost.
#[test]
fn the_unrendered_source_refusal_stops_at_the_first_non_iterator_sysroot_adt() {
    let func = parse(BOUNDED_USER_ELEMENT);
    let value = collected_operand_ty(&func);

    // Non-vacuity: the unauthenticated ADT really is in there, under the
    // iterator's own pointer field.
    let rendered = format!("{value:?}");
    assert!(rendered.contains("core::iter::adapters::cloned::Cloned"), "{rendered}");
    assert!(rendered.contains("core::slice::iter::Iter"), "{rendered}");
    assert!(
        rendered.contains("mycrate::Item"),
        "planted violation is gone: the element type is no longer an unauthenticated ADT, \
         so this bundle no longer exercises the bound"
    );
    assert!(!trust_types::path_root_is_authenticated_sysroot_crate("mycrate::Item"));

    assert!(!ty_is_unbounded_sysroot_iterator(value), "over-decline: {rendered}");
    let op = func
        .body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func: callee, args, .. } if is_collect_sink(callee) => args.first(),
            _ => None,
        })
        .expect("the collect sink");
    assert!(
        collect_source_is_bounded_std_collection(&func, op, 0),
        "the genuine bounded collect must keep its grant"
    );
    assert_eq!(unbounded_rows(&func), 0);
}

/// The compacted-name half, which the marker refusal does not subsume: when the
/// compacted aggregate IS the deny-listed iterator, its NAME survives
/// (`compact_oversized_field` preserves an `Adt`/`Datatype` name), so the
/// deny-list can still refuse it — anywhere, not only under an iterator root.
#[test]
fn a_compacted_aggregate_is_still_refused_by_its_preserved_name() {
    let compacted_cycle = Ty::Datatype {
        name: "core::iter::adapters::cycle::Cycle".to_string(),
        variants: Vec::new(),
    };
    assert!(ty_is_unbounded_sysroot_iterator(&compacted_cycle));

    // …and a compacted aggregate that names nothing unbounded is NOT refused on
    // its own account — the refusal above is the name, not the compaction.
    let compacted_vec = Ty::Datatype { name: "alloc::vec::Vec".to_string(), variants: Vec::new() };
    assert!(!ty_is_unbounded_sysroot_iterator(&compacted_vec));
    assert!(!ty_is_unbounded_sysroot_iterator(&Ty::adt(
        "alloc::vec::into_iter::IntoIter",
        vec![("buf".to_string(), compacted_vec)]
    )));
}

// ======================================================================
// 2. The STRING side: the receiver operand's own type
// ======================================================================

/// FALSIFY-ONCE for [`producer_receiver_value_is_authenticated_sysroot`]. The
/// planted violation is asserted first and is the round-3 hole exactly: on the
/// bundle as the PATCHED producer renders it, the string-side receiver anchor
/// still says `true`, because the impersonator's crate name reaches that string
/// only as a qualified SELF TYPE and the stamp is keyed on the callee's DEFINING
/// crate.
#[test]
fn the_receiver_operand_type_is_authenticated_not_only_the_rendered_string() {
    let func = with_producer_stamp(RANGEFROM_EXPLOIT);
    let (callee, args) = func
        .body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func, args, .. } if callee_tail(func) == "into_iter" => {
                Some((func.clone(), args.clone()))
            }
            _ => None,
        })
        .expect("the `into_iter` producer call");

    assert_eq!(
        callee, "<&std::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter",
        "the measured spelling: the impersonator's name is the SELF type of a real-`core` \
         trait method"
    );
    assert!(
        producer_receiver_is_authenticated_sysroot(&callee),
        "planted violation is gone: the STRING-side anchor now refuses this callee, so the \
         operand-side check below is no longer what closes it"
    );
    assert!(
        is_std_collection_iter_producer(&callee, "into_iter"),
        "planted violation is gone: the path-shape predicate no longer grants"
    );

    // The operand's own type is where the producer's stamp actually lands.
    assert!(!producer_receiver_value_is_authenticated_sysroot(&func, &args));
    match operand_place_ty(&func, &args[0]).expect("receiver type") {
        Ty::Ref { inner, .. } => match &**inner {
            Ty::Adt { name, .. } => assert!(name.starts_with(IMPERSONATOR_STAMP), "{name}"),
            other => panic!("{other:?}"),
        },
        other => panic!("{other:?}"),
    }
}

/// The other direction: the conjunct must not decline the shapes real bundles
/// carry. These five are the RECEIVER types MEASURED at the six genuine
/// bounded-source grant sites of the 2 572-bundle corpus — four slices (one with
/// a `TyKind::Param` element, one with a tuple element), and one `alloc::vec::Vec`.
#[test]
fn the_receiver_conjunct_accepts_every_measured_grant_shape() {
    let unsupported =
        Ty::Unsupported { kind: "TyKind::Param".to_string(), detail: "S".to_string() };
    let accepted = [
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) },
        Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Slice { elem: Box::new(adt("level::Level")) }),
        },
        Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Slice {
                elem: Box::new(Ty::Tuple(vec![adt("name::Name"), adt("level::Level")])),
            }),
        },
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(unsupported) }) },
        adt("alloc::vec::Vec"),
        Ty::Ref { mutable: false, inner: Box::new(Ty::Str) },
    ];
    for ty in &accepted {
        let func = receiver_probe_bundle(ty.clone());
        assert!(
            producer_receiver_value_is_authenticated_sysroot(&func, &probe_args()),
            "measured grant shape declined: {ty:?}"
        );
    }

    let refused = [
        // the impersonator, as the patched type-name renderer stamps it
        adt(&format!("{IMPERSONATOR_STAMP}std::vec::Vec")),
        Ty::Ref {
            mutable: false,
            inner: Box::new(adt(&format!("{IMPERSONATOR_STAMP}std::vec::Vec"))),
        },
        // an ordinary user collection
        adt("mycrate::vec::Vec"),
        // a bare type parameter, and the historical hand-built placeholder
        Ty::Unsupported { kind: "TyKind::Param".to_string(), detail: "C".to_string() },
        Ty::u32(),
    ];
    for ty in &refused {
        let func = receiver_probe_bundle(ty.clone());
        assert!(
            !producer_receiver_value_is_authenticated_sysroot(&func, &probe_args()),
            "receiver must fail closed: {ty:?}"
        );
    }

    // No receiver argument at all fails closed too.
    let func = receiver_probe_bundle(adt("alloc::vec::Vec"));
    assert!(!producer_receiver_value_is_authenticated_sysroot(&func, &[]));
}

/// `operand_place_ty` resolves the projections a receiver actually wears —
/// `s.items.iter()` lowers to a call on `Copy((_1.0))` — and declines the ones it
/// cannot answer, which every caller reads as a refusal.
#[test]
fn the_receiver_type_is_resolved_through_deref_and_field_projections() {
    let inner = adt("alloc::vec::Vec");
    let func = receiver_probe_bundle(Ty::adt(
        "mycrate::Holder",
        vec![("items".to_string(), inner.clone())],
    ));
    let field = Operand::Copy(Place { local: 1, projections: vec![Projection::Field(0)] });
    assert!(
        matches!(operand_place_ty(&func, &field), Some(Ty::Adt { name, .. }) if name == "alloc::vec::Vec")
    );
    assert!(producer_receiver_value_is_authenticated_sysroot(&func, std::slice::from_ref(&field)));

    // The holder itself is a user ADT and stays refused.
    assert!(!producer_receiver_value_is_authenticated_sysroot(&func, &probe_args()));

    // A `Deref` through a reference, and a projection this cannot answer.
    let reffed = receiver_probe_bundle(Ty::Ref { mutable: false, inner: Box::new(inner) });
    let deref = Operand::Copy(Place { local: 1, projections: vec![Projection::Deref] });
    assert!(
        matches!(operand_place_ty(&reffed, &deref), Some(Ty::Adt { name, .. }) if name == "alloc::vec::Vec")
    );
    let indexed = Operand::Copy(Place { local: 1, projections: vec![Projection::Index(2)] });
    assert!(operand_place_ty(&reffed, &indexed).is_none());
    assert!(operand_place_ty(&reffed, &Operand::Constant(ConstValue::Int(3))).is_none());
}

fn probe_args() -> Vec<Operand> {
    vec![Operand::Copy(Place::local(1))]
}

/// A one-local bundle whose local 1 carries `receiver_ty` — the minimum needed to
/// ask [`producer_receiver_value_is_authenticated_sysroot`] a question.
fn receiver_probe_bundle(receiver_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "probe".to_string(),
        def_path: "test::probe".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: receiver_ty, name: Some("recv".into()) },
            ],
            blocks: vec![],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ======================================================================
// 3. Neither repair is a substitute for the other
// ======================================================================

/// Each half ALONE closes the `RangeFrom` exploit, and the test says which is
/// which by removing the other's evidence rather than by reasoning about it.
///
/// * value side alone: the bundle VERBATIM, with no stamp anywhere — the string
///   anchor authenticates the forgery and the row survives only because
///   `RangeFrom` is refused;
/// * string side alone: the same bundle with the producer's stamp and the
///   iterator's type replaced by a genuinely BOUNDED sysroot iterator, so the
///   boundedness refusal has nothing to say and only the receiver operand does.
#[test]
fn each_half_alone_closes_the_rangefrom_shape() {
    assert!(
        !trust_types::path_has_unauthenticated_crate_stamp(RANGEFROM_EXPLOIT),
        "non-vacuity: the verbatim bundle carries no stamp at all"
    );
    assert_eq!(unbounded_rows(&parse(RANGEFROM_EXPLOIT)), 1, "value side alone");

    let bounded_value =
        RANGEFROM_EXPLOIT.replace("core::ops::range::RangeFrom", "alloc::vec::into_iter::IntoIter");
    let bounded = with_producer_stamp(&bounded_value);
    assert!(
        !ty_is_unbounded_sysroot_iterator(
            crate::local_ty_ref(&bounded, 2).expect("the iterator local")
        ),
        "planted violation is gone: the substituted value type is refused as unbounded, so \
         this case no longer isolates the receiver conjunct"
    );
    assert_eq!(unbounded_rows(&bounded), 1, "string side alone");
}
