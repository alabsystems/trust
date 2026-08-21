// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **I5 — CONTROLS ON THE GATED MINT DECISION.**
//!
//! The invariant `decide_mint` exists to enforce:
//!
//! > no `DefId` is minted without a total carrier AND `KernelChecked` AND an
//! > empty axiom closure
//!
//! Three preconditions, so four cases matter: one grant and three distinct
//! refusals. A decision procedure that refused everything would satisfy the
//! invariant vacuously, so the grant case is as load-bearing as the refusals.
//!
//! # On constructing a `KernelChecked` status in a test
//!
//! `KernelVerdict` has no public constructor. The only route is
//! `CicKernelRecheck::held_by_kernel_recheck()`, whose docs say plainly: *"The
//! name is an assertion, and it is meant to read as one at the call site."* Its
//! contract — the kernel re-checked THIS declaration's own obligation, the
//! caller can produce the exact term checked, and the caller ran the full
//! certification audit — is a contract this crate cannot verify.
//!
//! **A test may assert it; production may not.** That asymmetry is the point of
//! I2's sealing, and it is why these fixtures can exercise the grant path while
//! `def_collector` still cannot: a test is allowed to say "suppose the kernel
//! returned this", and the compiler is not. If you find yourself calling
//! `held_by_kernel_recheck()` in non-test code to make something compile, that
//! is the bug, not the seal.

use trust_clean_carrier::{carrier_at, CarrierRefused};
use trust_clean_origin::{decide_mint, MintRefusal};
use trust_symbols::{
    Assumption, AxiomClosure, CicKernelRecheck, KernelAuthority, KernelStatus, TermDigest,
};

/// `UInt64` — the fixed-width Clean type that carries exactly at `u64`.
fn uint64_ty() -> clean_kernel::Expr {
    clean_kernel::Expr::const_(clean_kernel::Name::from_string("UInt64"), vec![])
}

/// `Nat` — unbounded, and therefore carried by nothing.
fn nat_ty() -> clean_kernel::Expr {
    clean_kernel::Expr::const_(clean_kernel::Name::from_string("Nat"), vec![])
}

fn u64_ty() -> trust_types::Ty {
    trust_types::Ty::Int { width: 64, signed: false }
}

/// A `KernelChecked` status carrying the given closure. See the module docs for
/// why a test is permitted to mint this.
fn kernel_checked(closure: AxiomClosure) -> KernelStatus {
    CicKernelRecheck::held_by_kernel_recheck()
        .kernel_checked(TermDigest::of_bytes(b"a term the kernel re-checked"), closure)
}

#[test]
fn grant_all_three_preconditions_present() {
    let status = kernel_checked(AxiomClosure::audited([]));
    let carrier = carrier_at(&uint64_ty(), &u64_ty());

    let grant = decide_mint("f", &status, carrier)
        .expect("kernel-checked + audited-empty closure + total carrier must MINT");

    assert_eq!(grant.name(), "f");
    assert_eq!(
        grant.carrier().rust(),
        &u64_ty(),
        "the grant must carry the carrier the DefId will be typed at"
    );
}

#[test]
fn refuse_not_kernel_checked() {
    // `Parsed` is the default status: a successful parse buys a name and a
    // sort, and at I5 it does not even buy a name in the value namespace.
    for status in [KernelStatus::Parsed, KernelStatus::Elaborated, KernelStatus::Reflected] {
        let refusal = decide_mint("f", &status, carrier_at(&uint64_ty(), &u64_ty())).expect_err(
            "a declaration the kernel did not re-check must never acquire a DefId, \
             however good its carrier is",
        );
        assert!(
            matches!(refusal, MintRefusal::NotKernelChecked { .. }),
            "expected NotKernelChecked for {status:?}; got {refusal:?}"
        );
    }
}

#[test]
fn refuse_reflected_carrier_specifically_and_say_so() {
    // I2's control, restated at the mint site. A `Reflected` symbol is a Rust
    // item projected INTO Clean by the R functor — the opposite direction. The
    // kernel checked that the carrier's body inhabits its type; it never
    // checked that the constant DENOTES the Rust `fn`. Minting a callable
    // `DefId` from one would close a loop through an unchecked correspondence.
    let refusal = decide_mint("f", &KernelStatus::Reflected, carrier_at(&uint64_ty(), &u64_ty()))
        .expect_err("a reflected carrier must be refused where KernelChecked is required");

    let note = refusal.note();
    assert!(
        note.contains("reflected"),
        "the note must name the reflected-carrier case specifically — that \
         distinction is the whole point of I2's seam. got:\n{note}"
    );
}

#[test]
fn refuse_unrecorded_axiom_closure_distinctly_from_nonempty() {
    // "We did not look" and "we looked and found nothing" are different facts.
    // `trust-symbols` forbids the former softening into the latter, so the two
    // must not collapse into one diagnostic.
    let refusal = decide_mint(
        "f",
        &kernel_checked(AxiomClosure::unrecorded()),
        carrier_at(&uint64_ty(), &u64_ty()),
    )
    .expect_err("an unrecorded closure is not an empty one and must refuse");

    assert!(
        matches!(refusal, MintRefusal::AxiomClosureUnrecorded { .. }),
        "an unrecorded closure must NOT be reported as a non-empty one; got {refusal:?}"
    );
}

#[test]
fn refuse_nonempty_axiom_closure_and_disclose_the_assumptions_by_name() {
    let closure = AxiomClosure::audited([
        Assumption::domain_axiom("key_lemma").expect("a nameable domain axiom"),
    ]);
    let refusal = decide_mint("f", &kernel_checked(closure), carrier_at(&uint64_ty(), &u64_ty()))
        .expect_err("a declaration resting on an undischarged assumption must refuse");

    match &refusal {
        MintRefusal::AxiomClosureNonEmpty { assumptions, .. } => {
            assert!(
                assumptions.iter().any(|a| a.contains("key_lemma")),
                "the axiom closure must be disclosed BY NAME, not merely counted; got \
                 {assumptions:?}"
            );
        }
        other => panic!("expected AxiomClosureNonEmpty; got {other:?}"),
    }

    assert!(
        refusal.note().contains("key_lemma"),
        "the v7/D3 note must name the assumption the user has to discharge"
    );
}

#[test]
fn refuse_when_no_total_carrier_exists() {
    // `Nat` is unbounded. There is no fixed-width carrier at any width, so no
    // `DefId` — this is the precondition that stands between a Clean `Nat` and
    // a wrapping `u64` in the emitted binary.
    let refusal = decide_mint(
        "f",
        &kernel_checked(AxiomClosure::audited([])),
        carrier_at(&nat_ty(), &u64_ty()),
    )
    .expect_err("Nat has no total u64 carrier, so `f` must not become callable");

    match &refusal {
        MintRefusal::NoTotalCarrier { refusal: carrier_refusal, .. } => {
            assert!(
                matches!(carrier_refusal, CarrierRefused::Narrowing { .. }),
                "expected I4's narrowing refusal, carried verbatim; got {carrier_refusal:?}"
            );
        }
        other => panic!("expected NoTotalCarrier; got {other:?}"),
    }
}

#[test]
fn every_refusal_note_offers_at_least_two_options() {
    // Ruling v7/D3: a refusal must carry the fix, WITH OPTIONS. A refusal with
    // exactly one escape is an ultimatum, and one with none is the defect the
    // ruling was written against.
    let refusals = vec![
        decide_mint("f", &KernelStatus::Parsed, carrier_at(&uint64_ty(), &u64_ty())).unwrap_err(),
        decide_mint(
            "f",
            &kernel_checked(AxiomClosure::unrecorded()),
            carrier_at(&uint64_ty(), &u64_ty()),
        )
        .unwrap_err(),
        decide_mint(
            "f",
            &kernel_checked(AxiomClosure::audited([
                Assumption::domain_axiom("key_lemma").unwrap()
            ])),
            carrier_at(&uint64_ty(), &u64_ty()),
        )
        .unwrap_err(),
        decide_mint(
            "f",
            &kernel_checked(AxiomClosure::audited([])),
            carrier_at(&nat_ty(), &u64_ty()),
        )
        .unwrap_err(),
    ];

    for refusal in &refusals {
        let note = refusal.note();
        let options = note.matches("\n- ").count();
        assert!(
            options >= 2,
            "v7/D3 requires OPTIONS; {refusal:?} offered {options}:\n{note}"
        );
        assert!(
            note.contains('f'),
            "the note must name the declaration it is about:\n{note}"
        );
    }
}
