// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Control 20 — a minted `DefId` carries the caller obligations its erased
//! hypothesis binders impose, and a door that cannot carry them cannot see
//! one.**
//!
//! `fa788aab89`'s consequence for gcd, verbatim: *"the obligation is real but
//! it is a PLAN-lane obligation, not a kernel one: it must constrain which MIR
//! gets built (a caller-side precondition on the minted `DefId`, or an emitted
//! `Assert`), and its discharge is an ordinary Rust obligation, never a
//! `Faithful` token."*
//!
//! This file pins the mint half of that: [`decide_mint_from_signature`] grants
//! with the obligations attached, and the older [`decide_mint`] — which takes
//! one `Carrier`, not a signature — cannot silently drop one, because a bare
//! `Carrier` is not a type a hypothesis can hide in.
//!
//! # What is deliberately NOT claimed here
//!
//! A grant is not an emission. `plan_clean_origin_body` still reads the
//! declaration's type through `carrier_signature_for` (the un-lifted door), so
//! a hypothesis-carrying `def` does not yet reach MIR. That residual is real
//! and is stated in the report rather than papered over: this control is about
//! the obligation SURVIVING the mint, which is the step that was structurally
//! impossible before.

use clean_kernel::{BinderInfo, Expr, Level, Name};
use trust_clean_carrier::{
    CarrierRefused, PreconditionOperand, carrier_at, carrier_signature_for,
    carrier_signature_with_hypotheses_for,
};
use trust_clean_origin::{MintRefusal, decide_mint, decide_mint_from_signature};
// `KernelAuthority` is the SEALED trait that owns `kernel_checked`; it must be
// in scope to mint a `KernelChecked` status at all, which is the seam working
// as designed (a crate that cannot name the kernel cannot fabricate one).
use trust_symbols::{AxiomClosure, CicKernelRecheck, KernelAuthority, KernelStatus, TermDigest};

fn c(n: &str) -> Expr {
    Expr::const_(Name::from_string(n), vec![])
}

fn uint64_ty() -> Expr {
    c("UInt64")
}

fn u64_ty() -> trust_types::Ty {
    trust_types::Ty::Int { width: 64, signed: false }
}

/// `@Ne UInt64 <a> <b>`.
fn ne(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
        [uint64_ty(), a, b],
    )
}

fn numeral(n: u64) -> Expr {
    Expr::app(c("UInt64.ofNat"), Expr::nat_lit(n))
}

fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, domain, body)
}

/// The type of `def safe_rem (a b : UInt64) (h : b ≠ 0) : UInt64`.
fn safe_rem_ty() -> Expr {
    pi(uint64_ty(), pi(uint64_ty(), pi(ne(Expr::bvar(0), numeral(0)), uint64_ty())))
}

/// A `KernelChecked` status with an audited-empty closure — the only status
/// that can mint. See `control_1_mint_preconditions.rs` for why a test may
/// construct one.
fn kernel_checked() -> KernelStatus {
    CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
        TermDigest::of_bytes(b"a term the kernel re-checked"),
        AxiomClosure::audited([]),
    )
}

// ---------------------------------------------------------------------------
// The grant carries the obligation
// ---------------------------------------------------------------------------

#[test]
fn a_hypothesis_carrying_declaration_mints_with_its_precondition() {
    let signature = carrier_signature_with_hypotheses_for(&safe_rem_ty());
    let grant = decide_mint_from_signature("safe_rem", &kernel_checked(), signature)
        .expect("kernel-checked + audited-empty closure + total carriers must MINT");

    assert_eq!(grant.name(), "safe_rem");
    assert_eq!(
        grant.carrier().rust(),
        &u64_ty(),
        "the grant is typed at the RESULT carrier, unchanged by the lift"
    );

    let obligations = grant.preconditions();
    assert_eq!(obligations.len(), 1, "the erased proof binder must leave an obligation behind");
    assert_eq!(obligations[0].left(), PreconditionOperand::Argument(1));
    assert_eq!(obligations[0].right(), PreconditionOperand::Literal(0));
    assert_eq!(obligations[0].width(), 64);
}

#[test]
fn an_ordinary_declaration_mints_with_no_obligations() {
    // The whole point of "smallest sound increment": nothing changes for a
    // declaration that has no hypothesis. An empty obligation list is not a
    // withheld one.
    let signature = carrier_signature_with_hypotheses_for(&Expr::arrow(uint64_ty(), uint64_ty()));
    let grant = decide_mint_from_signature("id64", &kernel_checked(), signature).expect("mints");
    assert!(grant.preconditions().is_empty());
}

// ---------------------------------------------------------------------------
// The old door cannot drop one, because it cannot see one
// ---------------------------------------------------------------------------

#[test]
fn the_carrier_door_grants_no_preconditions_and_never_saw_a_hypothesis() {
    // `decide_mint` takes ONE `Carrier`. A `Carrier` is a single position's
    // evidence; there is no hypothesis binder inside it to lose. So "the caller
    // forgot to forward the obligations" is not a reachable state on this door
    // — it is a shape that does not exist.
    let grant = decide_mint("f", &kernel_checked(), carrier_at(&uint64_ty(), &u64_ty()))
        .expect("unchanged behaviour");
    assert!(grant.preconditions().is_empty());
}

#[test]
fn the_unlifted_signature_door_still_refuses_the_hypothesis_type_outright() {
    // A consumer that has not opted into the lift gets a REFUSAL, not a
    // signature with obligations it would silently drop. That is what makes the
    // lift additive rather than a widening.
    let refusal = decide_mint_from_signature(
        "safe_rem",
        &kernel_checked(),
        carrier_signature_for(&safe_rem_ty()),
    )
    .expect_err("the un-lifted door refuses a dependent Pi, as it always has");
    let MintRefusal::NoTotalCarrier { refusal: inner, .. } = &refusal else {
        panic!("expected NoTotalCarrier, got {refusal:?}");
    };
    assert!(matches!(inner, CarrierRefused::DependentFunctionType { .. }), "{inner:?}");
}

// ---------------------------------------------------------------------------
// The three original preconditions are unweakened by the lift
// ---------------------------------------------------------------------------

#[test]
fn a_hypothesis_does_not_buy_a_way_past_the_kernel_check() {
    for status in [KernelStatus::Parsed, KernelStatus::Elaborated, KernelStatus::Reflected] {
        let refusal = decide_mint_from_signature(
            "safe_rem",
            &status,
            carrier_signature_with_hypotheses_for(&safe_rem_ty()),
        )
        .expect_err("a declaration the kernel did not re-check never acquires a DefId");
        assert!(matches!(refusal, MintRefusal::NotKernelChecked { .. }), "{refusal:?}");
    }
}

#[test]
fn a_hypothesis_does_not_buy_a_way_past_the_axiom_closure() {
    let resting_on_sorry = CicKernelRecheck::held_by_kernel_recheck()
        .kernel_checked(TermDigest::of_bytes(b"t"), AxiomClosure::unrecorded());
    let refusal = decide_mint_from_signature(
        "safe_rem",
        &resting_on_sorry,
        carrier_signature_with_hypotheses_for(&safe_rem_ty()),
    )
    .expect_err("an unrecorded closure is not an empty one");
    assert!(matches!(refusal, MintRefusal::AxiomClosureUnrecorded { .. }), "{refusal:?}");
}

#[test]
fn an_unstatable_hypothesis_refuses_the_mint_and_the_note_carries_the_fix() {
    // `(a b : UInt64) -> (h : a < b) -> UInt64`. The hypothesis is real and
    // this compiler cannot state it, so the declaration does NOT become
    // callable — erasing it would advertise a weaker contract than the kernel
    // checked. v7/D3: the refusal names the supported form and the options.
    let lt = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [uint64_ty(), c("instLTUInt64"), Expr::bvar(1), Expr::bvar(0)],
    );
    let ty = pi(uint64_ty(), pi(uint64_ty(), pi(lt, uint64_ty())));

    let refusal = decide_mint_from_signature(
        "lt_guarded",
        &kernel_checked(),
        carrier_signature_with_hypotheses_for(&ty),
    )
    .expect_err("an unstatable hypothesis must refuse the mint");

    let note = refusal.note();
    assert!(note.contains("options:"), "a refusal with no next step is a defect:\n{note}");
    assert!(note.contains('≠'), "the note must name the hypothesis form that IS carried:\n{note}");
}
