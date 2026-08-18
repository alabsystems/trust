// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! # The `#![no_std]` sysroot impersonation — the hole the STAMP itself had
//!
//! The 2026-08-16 spoof fixture next door relies on the compiler having already
//! stamped the impersonator, because the real `alloc` was in the graph and the
//! DUPLICATE-CRATE-NAME rule fired. This module is the case where it does not.
//!
//! In a `#![no_std]` graph the real `std` is never injected, so a crate built
//! `--crate-name std` is the ONLY `std` in the graph, the duplicate-name test is
//! false, and BOTH authenticators are handed an unstamped sysroot root:
//!
//! ```text
//! callee   std::vec::Vec::<u8>::iter               (UNSTAMPED, root `std::`)
//! local 2  Ty::Adt { name: "std::vec::Endless" }   (UNSTAMPED, root `std::`)
//! ```
//!
//! MEASURED on `stage2/bin/trustc` at `0a3cd0152`: exit 0, zero diagnostics.
//! Byte-identical aux named `mycrate`: exit 1, two errors. Same for the
//! `.into_iter()` shape. See
//! `fixtures/no-std-sysroot-impersonation-2026-08-17/PROVENANCE.md`.
//!
//! A duplicate-name test is a UNIQUENESS test, not an authenticator. The producer
//! fix stamps on IDENTITY instead — `trust_mir_extract::convert::
//! impersonates_sysroot_crate`, whose sysroot identity comes from the compiler's
//! own lang/diagnostic-item anchors.
//!
//! THE BOUND, so nothing here is read as more than it is: those anchors are
//! ATTRIBUTES. An aux that writes `#![feature(rustc_attrs)]` and
//! `#[rustc_diagnostic_item = "HashMap"]` authenticates itself as `std` in a
//! graph where the real `std` is absent — MEASURED, and recorded as residual R2
//! on `impersonates_sysroot_crate`. The exploit closed here needs no internal
//! feature at all; that one does.
//!
//! WHAT THIS MODULE CAN AND CANNOT MEASURE. The four `.json` fixtures are verbatim
//! compiler output. The post-fix rendering is DERIVED here, by applying the
//! producer's two edited renderers as an explicit substitution — the compiler
//! carrying the fix was not built (`x.py` is out of scope). Everything downstream
//! of that substitution is production code on a real bundle. The substitution is
//! written out below rather than baked into extra fixture files precisely so a
//! reviewer can check it against the producer in one screen.

use super::*;

/// The `{:016x}` `StableCrateId` the compiler assigned to BOTH aux artifacts
/// built `--crate-name std`, read from `trustc -Zls=all`
/// (decimal 1127107163555717956). This is the value
/// `convert::sysroot_authenticated_path` puts in the stamp; it is measured, not
/// chosen. The real sysroot `std` in the same toolchain is 7398676898008484585 —
/// same NAME, different `StableCrateId`, which is the fix's entire input.
const IMPERSONATOR_STAMP: &str = "__trust_crate@0fa449fe5b896344::";

/// The four measured bundles. `*_ITER` is `v.iter().collect()`; `*_INTO_ITER` is
/// `v.into_iter().collect()`, whose producer callee belongs to the REAL `core`
/// and is therefore NOT reached by the callee stamp.
const EXPLOIT_ITER: &str = include_str!(
    "../../fixtures/no-std-sysroot-impersonation-2026-08-17/user_boom_impersonating_std.json"
);
const CONTROL_ITER: &str = include_str!(
    "../../fixtures/no-std-sysroot-impersonation-2026-08-17/user_boom_ordinary_crate_name.json"
);
const EXPLOIT_INTO_ITER: &str = include_str!(
    "../../fixtures/no-std-sysroot-impersonation-2026-08-17/user_boom_impersonating_std_into_iter.json"
);
const CONTROL_INTO_ITER: &str = include_str!(
    "../../fixtures/no-std-sysroot-impersonation-2026-08-17/user_boom_ordinary_crate_name_into_iter.json"
);

fn parse(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).unwrap_or_else(|e| panic!("parse fixture: {e}"))
}

/// Which producer renderer the fix is being asked to run.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Stamp {
    /// `convert::direct_call_def_path`, rule 2 — stamps a callee whose DEFINING
    /// crate is the impersonator.
    Callee,
    /// `lib::sysroot_authenticated_def_path_str` — stamps every `Ty::Adt`/
    /// `Ty::Datatype`/`AggregateKind::Adt` NAME rendered from the impersonator.
    AdtName,
}

/// A bundle as the PATCHED producer would render it.
///
/// `callees` are the strings the impersonator owns AS A CALLEE def path (empty
/// for the `into_iter` shape — `IntoIterator::into_iter`'s `DefId` belongs to the
/// real `core`, so rule 2 does not fire on it, and that asymmetry is the point of
/// `only_the_type_name_stamp_closes_the_into_iter_shape`). `adts` are the type
/// NAMES it owns. Every other `std::`/`core::`/`alloc::` string in these bundles
/// belongs to the REAL sysroot crates and is deliberately left alone — which is
/// what makes this a fix and not a blanket refusal.
fn producer_stamped(
    json: &str,
    callees: &[&str],
    adts: &[&str],
    stamps: &[Stamp],
) -> VerifiableFunction {
    let mut json = json.to_string();
    if stamps.contains(&Stamp::Callee) {
        for callee in callees {
            let from = format!("\"func\": \"{callee}\"");
            assert!(json.contains(&from), "callee `{callee}` drifted in the fixture");
            json = json.replace(&from, &format!("\"func\": \"{IMPERSONATOR_STAMP}{callee}\""));
        }
    }
    if stamps.contains(&Stamp::AdtName) {
        for adt in adts {
            let from = format!("\"name\": \"{adt}\"");
            assert!(json.contains(&from), "ADT name `{adt}` drifted in the fixture");
            json = json.replace(&from, &format!("\"name\": \"{IMPERSONATOR_STAMP}{adt}\""));
        }
    }
    parse(&json)
}

fn iter_shape(stamps: &[Stamp]) -> VerifiableFunction {
    producer_stamped(
        EXPLOIT_ITER,
        &["std::vec::Vec::<u8>::iter"],
        &["std::vec::Endless", "std::vec::Vec"],
        stamps,
    )
}

fn into_iter_shape(stamps: &[Stamp]) -> VerifiableFunction {
    producer_stamped(EXPLOIT_INTO_ITER, &[], &["std::vec::Endless", "std::vec::Vec"], stamps)
}

/// Obligations the unbounded-allocation lane emits, in either form it uses — a
/// solvable `UnboundedAllocation` bound, or the visible `UnsupportedMir` row it
/// raises when the element count is not recoverable.
fn unbounded_alloc_vc_count(func: &VerifiableFunction) -> usize {
    generate_unbounded_allocation_vcs(func)
        .iter()
        .filter(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } => kind.contains("UnboundedAllocation"),
            other => format!("{other:?}").contains("UnboundedAllocation"),
        })
        .count()
}

fn producer_callee(func: &VerifiableFunction, tail: &str) -> String {
    let found: Vec<String> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } if callee_tail(func) == tail => Some(func.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(found.len(), 1, "exactly one `{tail}` call in the fixture: {found:?}");
    found[0].clone()
}

/// NON-VACUITY, and the correction of a claim this campaign shipped: these
/// bundles carry NO stamp at all. The duplicate-name rule did not fire, so the
/// earlier doc claim that an impersonator is "ALWAYS" caught by it is false on
/// these bytes.
#[test]
fn the_compiler_emitted_the_impersonators_paths_with_no_stamp_at_all() {
    for json in [EXPLOIT_ITER, EXPLOIT_INTO_ITER] {
        assert!(
            !trust_types::path_has_unauthenticated_crate_stamp(json),
            "the whole bundle must be stamp-free — that IS the finding"
        );
    }

    let iter = parse(EXPLOIT_ITER);
    assert_eq!(producer_callee(&iter, "iter"), "std::vec::Vec::<u8>::iter");

    let into_iter = parse(EXPLOIT_INTO_ITER);
    assert_eq!(
        producer_callee(&into_iter, "into_iter"),
        "<&std::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter"
    );

    // The iterator local's type — the value-side authenticator's whole input —
    // is the SAME forged ADT in both shapes.
    for func in [&iter, &into_iter] {
        match crate::local_ty_ref(func, 2).expect("local 2 has a type") {
            Ty::Adt { name, .. } => {
                assert_eq!(name, "std::vec::Endless");
                assert!(trust_types::path_root_is_authenticated_sysroot_crate(name));
            }
            other => panic!("local 2 is not an ADT: {other:?}"),
        }
    }

    // The controls rename one crate and nothing else.
    assert_eq!(producer_callee(&parse(CONTROL_ITER), "iter"), "mycrate::vec::Vec::<u8>::iter");
    assert_eq!(
        producer_callee(&parse(CONTROL_INTO_ITER), "into_iter"),
        "<&mycrate::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter"
    );
}

/// FALSIFY-ONCE at the OBLIGATION, both states, on the production entry point,
/// for both shapes.
///
/// BEFORE (planted violation, asserted so the AFTER cannot pass vacuously): the
/// unstamped exploit bundles emit ZERO unbounded-allocation obligations, while
/// the controls — the same programs with one crate renamed — emit one each.
/// AFTER: with the producer's identity stamps applied, each exploit emits its
/// control's obligation.
#[test]
fn the_producer_identity_stamp_restores_the_deleted_obligation() {
    for (exploit, control, stamped) in [
        (EXPLOIT_ITER, CONTROL_ITER, iter_shape(&[Stamp::Callee, Stamp::AdtName])),
        (EXPLOIT_INTO_ITER, CONTROL_INTO_ITER, into_iter_shape(&[Stamp::Callee, Stamp::AdtName])),
    ] {
        let control = unbounded_alloc_vc_count(&parse(control));
        assert!(
            control >= 1,
            "planted violation is gone: the ordinary-crate-name control no longer emits an \
             unbounded-allocation obligation, so the exploit measurement proves nothing"
        );
        assert_eq!(
            unbounded_alloc_vc_count(&parse(exploit)),
            0,
            "planted violation is gone: the UNSTAMPED exploit bundle is already refused, so \
             the producer fix cannot be what closes it"
        );
        assert_eq!(
            unbounded_alloc_vc_count(&stamped),
            control,
            "with the producer's identity stamps the impersonator must carry the SAME \
             obligation as the ordinary-crate-name control"
        );
    }
}

/// THE TYPE-NAME STAMP IS NOT REDUNDANT — measured on real compiler bytes.
///
/// `v.into_iter()` renders its producer as
/// `<&std::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter`,
/// whose `DefId` belongs to the REAL `core`. Rule 2 keys on the callee's own
/// defining crate, so the callee stamp is a NO-OP on this shape and the receiver
/// anchor reads the impersonator's `std::vec::Vec` straight out of the string.
/// Only the `Ty::Adt` name stamp closes it — which is the whole reason the second
/// half of this fix exists.
#[test]
fn only_the_type_name_stamp_closes_the_into_iter_shape() {
    assert_eq!(
        unbounded_alloc_vc_count(&into_iter_shape(&[Stamp::Callee])),
        0,
        "planted violation is gone: the callee stamp now reaches the `into_iter` shape, so \
         this test no longer witnesses the gap the type-name stamp exists for"
    );
    assert!(unbounded_alloc_vc_count(&into_iter_shape(&[Stamp::AdtName])) >= 1);
}

/// The mirror of the above on the `.iter()` shape: there the impersonator DOES
/// own the producer callee, so either half alone suffices. Stated explicitly so
/// nobody generalizes from one shape to the other in either direction.
#[test]
fn on_the_iter_shape_each_half_alone_is_enough() {
    for stamps in [vec![Stamp::Callee], vec![Stamp::AdtName]] {
        assert!(
            unbounded_alloc_vc_count(&iter_shape(&stamps)) >= 1,
            "{stamps:?} alone must refuse the impersonated bounded-source grant"
        );
    }
}

/// The two authenticators at predicate level, on the exact strings the patched
/// producer renders. The row differentials above run through this seam; asserting
/// it directly stops a future change to either predicate from silently moving the
/// row test onto the other one.
#[test]
fn both_authenticators_refuse_the_stamped_spellings_and_keep_the_real_ones() {
    let stamped_callee = format!("{IMPERSONATOR_STAMP}std::vec::Vec::<u8>::iter");
    assert!(
        stamped_callee.contains("std::vec::"),
        "planted violation is gone: the pre-2026-08-16 unanchored substring test no longer \
         matches the stamped spelling"
    );
    assert!(!is_std_collection_iter_producer(&stamped_callee, callee_tail(&stamped_callee)));
    // Unstamped, it IS granted — which is the whole exploit.
    assert!(is_std_collection_iter_producer(
        "std::vec::Vec::<u8>::iter",
        callee_tail("std::vec::Vec::<u8>::iter")
    ));

    assert!(!ty_is_authenticated_std_iterator(&Ty::adt(
        format!("{IMPERSONATOR_STAMP}std::vec::Endless"),
        Vec::new()
    )));
    assert!(
        ty_is_authenticated_std_iterator(&Ty::adt("std::vec::Endless", Vec::new())),
        "planted violation is gone: the unstamped forged type is already refused, so the \
         producer-side type stamp is not what closes this half"
    );
}

/// PRECISION, the direction round 1 lost on: the genuine sysroot spellings that
/// sit in these very bundles are untouched. The impersonator owns a handful of
/// strings; the real `alloc`/`core` ones next to them keep authenticating, and a
/// real `core::slice` producer keeps its bounded-source grant.
#[test]
fn the_real_sysroot_spellings_in_the_same_bundle_are_not_disturbed() {
    for real in [
        "alloc::vec::Vec",
        "alloc::raw_vec::RawVec",
        "core::ptr::non_null::NonNull",
        "core::slice::<impl [u8]>::iter",
    ] {
        assert!(
            trust_types::path_root_is_authenticated_sysroot_crate(real),
            "genuine sysroot spelling refused: {real}"
        );
    }
    assert!(is_std_collection_iter_producer(
        "core::slice::<impl [u8]>::iter",
        callee_tail("core::slice::<impl [u8]>::iter")
    ));
    assert!(ty_is_authenticated_std_iterator(&Ty::adt("core::slice::iter::Iter<u8>", Vec::new())));
}

/// An impersonator's type spelled INSIDE a qualified `<Self as Trait>` callee
/// header is not stamped, because rule 2 keys on the callee's own defining crate.
/// The string-side receiver anchor therefore still authenticates it.
///
/// 2026-08-17 (round 4) CORRECTION, and this one was a live hole rather than
/// stale wording. This test shipped as residual R1 with the rationale *"the
/// conjunction with the value-side authenticator is what closes it — the one
/// place the two are load-bearing TOGETHER"*. That rationale was refuted by a
/// measured program: the value-side authenticator is a PROVENANCE test, so an
/// impersonator closes it by declaring `type IntoIter = core::ops::RangeFrom<u64>`
/// — a genuine, correctly-unstamped `core` ADT — and the consumer then compiled
/// with exit 0 and zero diagnostics. The residual is not closed by a conjunction
/// of two provenance tests; it is closed by reading the receiver OPERAND's own
/// `Ty` (`producer_receiver_value_is_authenticated_sysroot`), which the type-name
/// renderer does stamp, and independently by refusing endless sysroot iterators
/// on the value side. Both are pinned in `bounded_source_value_tests`; what
/// remains true here, and is all this test now claims, is that the STRING is
/// unstamped.
#[test]
fn a_qualified_self_type_from_the_impersonator_is_not_reached_by_the_callee_stamp() {
    // The measured spelling, from the real dump.
    let into_iter = producer_callee(&parse(EXPLOIT_INTO_ITER), "into_iter");
    assert!(into_iter.contains("std::vec::Vec"), "the Self type is spelled in the callee");
    assert!(
        !trust_types::path_has_unauthenticated_crate_stamp(&into_iter),
        "rule 2 keys on the CALLEE's defining crate (real `core` here), so this string is \
         unstamped even after the fix — the residual this test exists to pin"
    );
    assert!(
        producer_receiver_is_authenticated_sysroot(&into_iter),
        "planted violation is gone: the receiver anchor already refuses it, so the \
         value-side conjunct is not what closes this"
    );

    // Closed by the value side: the iterator local's TYPE carries the stamp.
    assert!(!ty_is_authenticated_std_iterator(&Ty::adt(
        format!("{IMPERSONATOR_STAMP}std::vec::Endless"),
        Vec::new()
    )));
}
