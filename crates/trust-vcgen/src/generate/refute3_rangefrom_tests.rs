// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! # The adversarial round-3 probe, as a REGRESSION test
//!
//! Provenance authentication was made exact over three rounds; this file is the
//! program that walked through all of it by handing out a GENUINE sysroot
//! iterator type. Neither producer stamp fires anywhere on the grant path,
//! because there is nothing to stamp: `core::ops::range::RangeFrom` belongs to
//! the real `core`.
//!
//! The assertions here are the round-3 reviewer's, INVERTED — they measured the
//! hole open and asserted `0` rows; they assert `1` now. Both states are recorded
//! in `bounded.md`: on the round-3 tree all three tests PASS in their original
//! form (0 rows for the exploit, 1 for the control) and FAIL in this form; on this
//! tree it is the other way round. The bundles are unchanged verbatim compiler
//! output; only the expected row counts moved.

use super::*;

const IMPERSONATOR_STAMP: &str = "__trust_crate@0fa449fe5b896344::";

const EXPLOIT: &str = include_str!("../../fixtures/refute3-rangefrom/exploit.json");
const CONTROL: &str = include_str!("../../fixtures/refute3-rangefrom/control.json");

fn parse(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).unwrap_or_else(|e| panic!("parse fixture: {e}"))
}

/// The bundle as the PATCHED producer renders it: rule 2 stamps every path whose
/// DEFINING crate is the impersonator. In this bundle that is exactly the ADT
/// name `std::vec::Vec` — the `into_iter` callee's `DefId` is the real `core`, and
/// `core::ops::range::RangeFrom` is the real `core`'s ADT.
fn fully_stamped() -> VerifiableFunction {
    let json = EXPLOIT.replace(
        "\"name\": \"std::vec::Vec\"",
        &format!("\"name\": \"{IMPERSONATOR_STAMP}std::vec::Vec\""),
    );
    assert!(json.contains(IMPERSONATOR_STAMP), "substitution must have applied");
    parse(&json)
}

/// The producer-side alternative the round-3 review offered as option (a): stamp
/// the impersonator's type where it appears as the QUALIFIED SELF TYPE of a
/// real-`core` trait callee. It closes the shape too — recorded here so the
/// consumer-side fix is not mistaken for the only possible one — but it needs
/// `rustc_middle` API that no test in this crate can reach.
fn stamped_including_qualified_self() -> VerifiableFunction {
    let json = EXPLOIT
        .replace(
            "\"name\": \"std::vec::Vec\"",
            &format!("\"name\": \"{IMPERSONATOR_STAMP}std::vec::Vec\""),
        )
        .replace("<&std::vec::Vec<u8>", &format!("<&{IMPERSONATOR_STAMP}std::vec::Vec<u8>"));
    parse(&json)
}

fn unbounded_alloc_vc_count(func: &VerifiableFunction) -> usize {
    generate_unbounded_allocation_vcs(func)
        .iter()
        .filter(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } => kind.contains("UnboundedAllocation"),
            other => format!("{other:?}").contains("UnboundedAllocation"),
        })
        .count()
}

#[test]
fn the_genuine_sysroot_iterator_type_is_gated_with_or_without_a_stamp() {
    // Non-vacuity: the verbatim bundle carries no stamp at all, so nothing below
    // is being closed by the producer's stamp.
    assert!(!trust_types::path_has_unauthenticated_crate_stamp(EXPLOIT));

    // The control (aux named `mycrate`) is gated, and always was.
    assert_eq!(unbounded_alloc_vc_count(&parse(CONTROL)), 1, "control must be gated");

    // The verbatim exploit is gated NOW — this is the row the round-3 tree
    // measured as 0. The value side alone does it: `RangeFrom` is refused as
    // unbounded before any producer question is asked.
    assert_eq!(unbounded_alloc_vc_count(&parse(EXPLOIT)), 1, "the round-3 hole, closed");

    // …and so is the bundle carrying both of round 3's producer stamps.
    assert_eq!(unbounded_alloc_vc_count(&fully_stamped()), 1);

    // The producer-side option (a) would also have closed it.
    assert_eq!(unbounded_alloc_vc_count(&stamped_including_qualified_self()), 1);
}

/// The mechanism, so the row count above is not read as coincidence: the grant
/// path is intact — the callee still authenticates as a std producer under the
/// string anchor — and the two round-4 conjuncts are what refuse it.
#[test]
fn the_grant_is_refused_at_the_receiver_operand_and_at_the_value() {
    let f = fully_stamped();
    let (callee, args) = f
        .body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func, args, .. } if callee_tail(func) == "into_iter" => {
                Some((func.clone(), args.clone()))
            }
            _ => None,
        })
        .expect("into_iter call");
    assert_eq!(
        callee, "<&std::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter",
        "rule 2 keys on the callee's own crate (real `core`), so this stays bare"
    );
    // Producer half, on the STRING: still authenticated, still matched as a std
    // collection producer. Nothing about the string changed in round 4.
    assert!(alloc_vcs::producer_receiver_is_authenticated_sysroot(&callee));
    assert!(alloc_vcs::is_std_collection_iter_producer(&callee, "into_iter"));
    // …and the receiver OPERAND, which the type-name renderer does stamp, refuses.
    assert!(!alloc_vcs::producer_receiver_value_is_authenticated_sysroot(&f, &args));

    // Value half: the iterator local is a REAL `core` ADT, so the ADT-name stamp
    // never touches it — and it is refused for being UNBOUNDED, not unauthentic.
    match crate::local_ty_ref(&f, 2).expect("local 2") {
        Ty::Adt { name, .. } => {
            assert_eq!(name, "core::ops::range::RangeFrom");
            assert!(trust_types::path_root_is_authenticated_sysroot_crate(name));
            assert!(alloc_vcs::ty_is_authenticated_std_iterator(
                crate::local_ty_ref(&f, 2).unwrap()
            ));
            assert_eq!(alloc_vcs::unbounded_sysroot_iterator_adt_name(name), Some("RangeFrom"));
        }
        other => panic!("local 2 is not an ADT: {other:?}"),
    }
    // The impersonator's own ADT name IS stamped — and it is now what the receiver
    // conjunct reads.
    match crate::local_ty_ref(&f, 1).expect("local 1") {
        Ty::Ref { inner, .. } => match &**inner {
            Ty::Adt { name, .. } => assert!(name.starts_with(IMPERSONATOR_STAMP)),
            other => panic!("{other:?}"),
        },
        other => panic!("{other:?}"),
    }
}

const EXPLOIT_DUP: &str = include_str!("../../fixtures/refute3-rangefrom/exploit_dupgraph.json");
const CONTROL_DUP: &str = include_str!("../../fixtures/refute3-rangefrom/control_dupgraph.json");

/// The SAME shape in an ORDINARY std graph — the real `std` IS loaded, so the
/// duplicate-name rule (rule 1) is TRUE — which the round-3 tree still let
/// through, because both stamp rules key on the CALLEE's own defining crate and
/// that is the real `core` here.
#[test]
fn the_ordinary_std_graph_is_gated_too() {
    assert!(!trust_types::path_has_unauthenticated_crate_stamp(EXPLOIT_DUP));
    assert_eq!(unbounded_alloc_vc_count(&parse(CONTROL_DUP)), 1, "control gated");
    assert_eq!(unbounded_alloc_vc_count(&parse(EXPLOIT_DUP)), 1, "verbatim: gated now");
    let stamped = EXPLOIT_DUP.replace(
        "\"name\": \"std::vec::Vec\"",
        &format!("\"name\": \"{IMPERSONATOR_STAMP}std::vec::Vec\""),
    );
    assert!(stamped.contains(IMPERSONATOR_STAMP));
    assert_eq!(unbounded_alloc_vc_count(&parse(&stamped)), 1, "stamped: gated now");
}
