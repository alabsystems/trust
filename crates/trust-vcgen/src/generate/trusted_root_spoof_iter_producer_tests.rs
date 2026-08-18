// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! # Trusted-root spoof, shape 5 — the CONSUMER that ignored the stamp
//!
//! The producer-side fix stamps a def path whose crate name is not a usable
//! identity (`__trust_crate@<id>::`). That is a fact about the string; it makes
//! a fail-closed check POSSIBLE, it is not itself a check. This module is the
//! measurement that one consumer was not performing it.
//!
//! `is_std_collection_iter_producer` tested `callee.contains("alloc::vec::")`.
//! A substring test cannot tell a root from a suffix, so the stamped spelling
//! matched, and a `true` from that matcher makes
//! `generate_unbounded_allocation_vcs` `continue` past the whole collect — the
//! obligation is not weakened, it is DELETED.
//!
//! Every fixture below is a verbatim `-Ztrust-dump=mir:` dump of the shipped
//! compiler; see `fixtures/trusted-root-spoof-endless-iter-2026-08-16/
//! PROVENANCE.md` for the exact command lines and the measured compiler
//! verdicts (exploit: exit 0, zero obligations; control: two obligations and a
//! build error). Nothing here is hand-built, and nothing here is hand-stamped:
//! the stamp in the exploit fixture was minted by the compiler's own
//! duplicate-crate-name rule, so this hole is reachable on unmodified `main`.

use super::*;

fn fixture(name: &str) -> VerifiableFunction {
    let json = match name {
        "impersonating_alloc" => include_str!(
            "../../fixtures/trusted-root-spoof-endless-iter-2026-08-16/user_boom_impersonating_alloc.json"
        ),
        "ordinary_crate_name" => include_str!(
            "../../fixtures/trusted-root-spoof-endless-iter-2026-08-16/user_boom_ordinary_crate_name.json"
        ),
        "real_std" => include_str!(
            "../../fixtures/trusted-root-spoof-endless-iter-2026-08-16/stdctl_fine_real_std.json"
        ),
        other => panic!("unknown trusted-root spoof iter fixture: {other}"),
    };
    serde_json::from_str(json).unwrap_or_else(|e| panic!("parse {name} fixture: {e}"))
}

/// The single `iter()` callee spelling the extractor put in the fixture.
fn iter_callee(func: &VerifiableFunction) -> String {
    let found: Vec<&String> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func),
            _ => None,
        })
        .filter(|c| callee_tail(c) == "iter")
        .collect();
    assert_eq!(found.len(), 1, "exactly one `iter` call in the fixture: {found:?}");
    found[0].clone()
}

/// Obligations the unbounded-allocation lane emits for `func`, in either of the
/// two forms it uses: a solvable `UnboundedAllocation` bound, or the visible
/// `UnsupportedMir` row (preclassified Unknown, never PROVEd) it raises when the
/// element count is not recoverable from optimized MIR. `collect` over an opaque
/// source takes the second road — which is exactly the row the shipped compiler
/// reported for the control run and did NOT report for the exploit run.
fn unbounded_alloc_vc_count(func: &VerifiableFunction) -> usize {
    generate_unbounded_allocation_vcs(func)
        .iter()
        .filter(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } => kind.contains("UnboundedAllocation"),
            other => format!("{other:?}").contains("UnboundedAllocation"),
        })
        .count()
}

/// NON-VACUITY: the fixtures really carry the spellings the shipped compiler
/// produced, and the exploit one really is stamped BY THE COMPILER.
#[test]
fn the_fixtures_carry_the_measured_extractor_spellings() {
    let spoof = iter_callee(&fixture("impersonating_alloc"));
    assert_eq!(
        spoof,
        "__trust_crate@1973d11b2baa21fa::alloc::vec::Vec::<u8>::iter\
         ::<__trust_args@9eb75f82a1f1d141819e81715e8e7e0e>"
    );
    assert!(trust_types::path_has_unauthenticated_crate_stamp(&spoof));

    let control = iter_callee(&fixture("ordinary_crate_name"));
    assert_eq!(control, "mycrate::vec::Vec::<u8>::iter");

    let real = iter_callee(&fixture("real_std"));
    assert_eq!(real, "core::slice::<impl [u8]>::iter");
    assert!(trust_types::path_root_is_authenticated_sysroot_crate(&real));
}

/// FALSIFY-ONCE for the matcher, both observed states.
///
/// BEFORE (the planted violation, asserted here so this test cannot pass
/// vacuously): the exact substring test the matcher used to perform still
/// matches the stamped spelling. AFTER: the matcher declines it.
#[test]
fn an_unauthenticated_alloc_cannot_buy_bounded_iterator_treatment() {
    let spoof = iter_callee(&fixture("impersonating_alloc"));
    assert!(
        spoof.contains("alloc::vec::"),
        "planted violation is gone: the old unanchored test no longer matches `{spoof}`, \
         so this test proves nothing"
    );
    assert_eq!(callee_tail(&spoof), "iter", "the tail arm must also still match");
    assert!(
        !is_std_collection_iter_producer(&spoof, callee_tail(&spoof)),
        "a stamped crate must not be read as a std collection: {spoof}"
    );

    // The genuine std producer, byte-identical to what the extractor emits for
    // it, is still recognized — the fix is an anchor, not a blanket refusal.
    let real = iter_callee(&fixture("real_std"));
    assert!(
        is_std_collection_iter_producer(&real, callee_tail(&real)),
        "the real std producer must keep its bounded-source treatment: {real}"
    );
}

/// The same two states at the OBLIGATION the matcher deletes, on the real
/// bundles. This is the reachability half: it is `generate_unbounded_allocation_vcs`
/// — the production entry point, over production MIR — that decides.
#[test]
fn the_deleted_unbounded_allocation_obligation_comes_back() {
    // Non-vacuity: the obligation genuinely exists for this program shape. The
    // ONLY difference between these two bundles is the aux crate's name.
    let control = fixture("ordinary_crate_name");
    assert!(
        unbounded_alloc_vc_count(&control) >= 1,
        "planted violation is gone: the ordinary-crate-name control no longer emits an \
         unbounded-allocation obligation, so the exploit fixture proves nothing"
    );

    let spoof = fixture("impersonating_alloc");
    assert!(
        unbounded_alloc_vc_count(&spoof) >= 1,
        "the impersonating-`alloc` bundle must carry the same obligation as the control: \
         its `iter()` is the SAME endless iterator, only the crate name differs"
    );

    // Precision control: a real `Vec::iter().copied().collect()` stays free of
    // the obligation, exactly as before the fix.
    let real = fixture("real_std");
    assert_eq!(
        unbounded_alloc_vc_count(&real),
        0,
        "a genuine bounded std collection source must still be waved through"
    );
}
