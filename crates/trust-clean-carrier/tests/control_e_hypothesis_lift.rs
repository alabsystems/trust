// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Control E — the dependent-`Pi` refusal is lifted for hypothesis binders,
//! and for nothing else.**
//!
//! `fa788aab89` measured the blocker for the ratified gcd route: *"a
//! hypothesis-carrying declaration cannot even be minted today — its type is a
//! dependent `Pi`, and `carrier_signature_for` refuses with
//! `DependentFunctionType`."* This file pins the lift that removes exactly that
//! blocker and no more.
//!
//! The three properties, one section each:
//!
//! 1. **The old door did not move.** `carrier_signature_for` still refuses
//!    every dependent `Pi`, hypothesis or not. That is what makes the lift
//!    additive: a consumer that was never taught to forward obligations cannot
//!    be handed a signature carrying them.
//! 2. **The new door admits the hypothesis case, with the obligation.** Arity
//!    drops the proof binder, the carriers are the value binders', and the
//!    precondition is `b != 0` over the CARRIED argument index.
//! 3. **Everything adjacent still refuses.** A dependent VALUE position, a
//!    dependent RESULT, a proof used downstream, a hypothesis over another
//!    proof, and a proposition the recogniser cannot state — each one is a
//!    refusal with its own reason, because each one would otherwise erase a
//!    requirement the kernel checked.

use clean_kernel::{BinderInfo, Expr, Level, Name};
use trust_clean_carrier::{
    CarrierRefused, PreconditionOperand, PreconditionRelation, carrier_signature_for,
    carrier_signature_with_hypotheses_for,
};

fn c(n: &str) -> Expr {
    Expr::const_(Name::from_string(n), vec![])
}

fn uint64() -> Expr {
    c("UInt64")
}

/// `@Ne UInt64 <a> <b>`.
fn ne(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]), [
        uint64(),
        a,
        b,
    ])
}

/// `UInt64.ofNat n`.
fn numeral(n: u64) -> Expr {
    Expr::app(c("UInt64.ofNat"), Expr::nat_lit(n))
}

fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, domain, body)
}

/// `(a b : UInt64) -> (h : b ≠ 0) -> UInt64`
///
/// The type of `def safe_rem (a b : UInt64) (h : b ≠ 0) : UInt64`. Under the
/// two value binders, `b` is `bvar(0)`.
fn safe_rem_ty() -> Expr {
    pi(uint64(), pi(uint64(), pi(ne(Expr::bvar(0), numeral(0)), uint64())))
}

// ---------------------------------------------------------------------------
// 1. The old door did not move
// ---------------------------------------------------------------------------

#[test]
fn carrier_signature_for_still_refuses_the_hypothesis_type() {
    let err = carrier_signature_for(&safe_rem_ty())
        .expect_err("the pre-existing door must be byte-identical to before the lift");
    assert!(
        matches!(err, CarrierRefused::DependentFunctionType { .. }),
        "the measured refusal `fa788aab89` recorded must still be what this door reports; \
         got {err:?}"
    );
}

#[test]
fn a_signature_from_the_old_door_carries_no_obligations_to_forget() {
    // Non-dependent, so it grants — and its obligation list is empty, which is
    // why every existing consumer of `carrier_signature_for` is unaffected.
    let sig = carrier_signature_for(&Expr::arrow(uint64(), uint64())).expect("exact both ways");
    assert!(sig.hypotheses().is_empty());
    assert!(sig.preconditions().is_empty());
}

// ---------------------------------------------------------------------------
// 2. The new door admits the hypothesis case, WITH the obligation
// ---------------------------------------------------------------------------

#[test]
fn the_hypothesis_binder_is_erased_and_becomes_a_caller_obligation() {
    let sig = carrier_signature_with_hypotheses_for(&safe_rem_ty())
        .expect("a recognised hypothesis must not sink the signature");

    // The proof binder is ERASED: arity counts carried values only.
    assert_eq!(sig.arity(), 2, "the proof argument is not a Rust parameter");
    assert_eq!(sig.arguments()[0].rust(), &trust_types::Ty::Int { width: 64, signed: false });
    assert_eq!(sig.arguments()[1].rust(), &trust_types::Ty::Int { width: 64, signed: false });
    assert_eq!(sig.result().rust(), &trust_types::Ty::Int { width: 64, signed: false });

    // …and the requirement it stood for is carried forward, not dropped.
    let obligations = sig.preconditions();
    assert_eq!(obligations.len(), 1, "one hypothesis, one obligation");
    let ob = &obligations[0];
    assert_eq!(ob.relation(), PreconditionRelation::NotEqual);
    assert_eq!(
        ob.left(),
        PreconditionOperand::Argument(1),
        "the obligation must name the CARRIED index of `b` — argument 1 — not its \
         telescope binder index or its de Bruijn level"
    );
    assert_eq!(ob.right(), PreconditionOperand::Literal(0));
    assert_eq!(ob.width(), 64);

    // The hypothesis records where it was, and that index counts ALL binders.
    assert_eq!(sig.hypotheses()[0].binder_index(), 2);
}

#[test]
fn a_hypothesis_relating_two_arguments_is_carried_too() {
    // `(a b : UInt64) -> (h : a ≠ b) -> UInt64`
    let ty = pi(uint64(), pi(uint64(), pi(ne(Expr::bvar(1), Expr::bvar(0)), uint64())));
    let sig = carrier_signature_with_hypotheses_for(&ty).expect("granted");
    let ob = &sig.preconditions()[0];
    assert_eq!(ob.left(), PreconditionOperand::Argument(0));
    assert_eq!(ob.right(), PreconditionOperand::Argument(1));
}

#[test]
fn two_hypotheses_both_travel() {
    // `(a b : UInt64) -> (h1 : b ≠ 0) -> (h2 : a ≠ 0) -> UInt64`.
    // Under three open binders `a` is bvar(2) and `b` is bvar(1).
    let ty = pi(
        uint64(),
        pi(
            uint64(),
            pi(ne(Expr::bvar(0), numeral(0)), pi(ne(Expr::bvar(2), numeral(0)), uint64())),
        ),
    );
    let sig = carrier_signature_with_hypotheses_for(&ty).expect("granted");
    assert_eq!(sig.arity(), 2);
    let obligations = sig.preconditions();
    assert_eq!(obligations.len(), 2);
    assert_eq!(obligations[0].left(), PreconditionOperand::Argument(1));
    assert_eq!(obligations[1].left(), PreconditionOperand::Argument(0));
}

#[test]
fn the_new_door_agrees_with_the_old_one_on_every_hypothesis_free_type() {
    // The lift is a strict extension: where there is no hypothesis binder, the
    // two functions must be indistinguishable — same grants, same refusals.
    let cases = [
        Expr::arrow(uint64(), uint64()),
        Expr::arrow(c("UInt8"), Expr::arrow(c("Bool"), c("UInt32"))),
        uint64(),
        // Refusals, too.
        Expr::arrow(c("Nat"), uint64()),
        Expr::arrow(uint64(), c("Int")),
        Expr::arrow(c("Prop"), uint64()),
        // A genuinely dependent VALUE position.
        pi(uint64(), Expr::app(c("Vec"), Expr::bvar(0))),
    ];
    for ty in cases {
        let old = carrier_signature_for(&ty);
        let new = carrier_signature_with_hypotheses_for(&ty);
        assert_eq!(
            old.is_ok(),
            new.is_ok(),
            "the two doors disagreed on whether to grant {ty:?}"
        );
        if let (Ok(old), Ok(new)) = (&old, &new) {
            assert_eq!(old.arity(), new.arity());
            assert_eq!(old.arguments(), new.arguments());
            assert_eq!(old.result(), new.result());
            assert!(new.preconditions().is_empty());
        }
    }
}

// ---------------------------------------------------------------------------
// 3. Everything adjacent still refuses
// ---------------------------------------------------------------------------

#[test]
fn a_dependent_value_position_is_still_refused_by_the_new_door() {
    // `(a : UInt64) -> Vec a`. Nothing about the lift touches this.
    let ty = pi(uint64(), Expr::app(c("Vec"), Expr::bvar(0)));
    let err = carrier_signature_with_hypotheses_for(&ty).expect_err("still refused");
    assert!(matches!(err, CarrierRefused::DependentFunctionType { .. }), "{err:?}");
}

#[test]
fn a_result_that_depends_on_the_proof_is_refused() {
    // `(b : UInt64) -> (h : b ≠ 0) -> P h`. The value produced depends on WHICH
    // proof was supplied; there is no Rust type for that, so the original
    // refusal stands even though the hypothesis itself is recognised.
    let ty = pi(uint64(), pi(ne(Expr::bvar(0), numeral(0)), Expr::app(c("P"), Expr::bvar(0))));
    let err = carrier_signature_with_hypotheses_for(&ty)
        .expect_err("erasing a proof the result depends on would be exactly the wrong binary");
    assert!(matches!(err, CarrierRefused::DependentFunctionType { .. }), "{err:?}");
}

#[test]
fn a_value_argument_after_a_proof_may_not_depend_on_it() {
    // `(b : UInt64) -> (h : b ≠ 0) -> (v : Vec h) -> UInt64`.
    let ty = pi(
        uint64(),
        pi(
            ne(Expr::bvar(0), numeral(0)),
            pi(Expr::app(c("Vec"), Expr::bvar(0)), uint64()),
        ),
    );
    assert!(
        carrier_signature_with_hypotheses_for(&ty).is_err(),
        "a later position depending on the erased proof must refuse"
    );
}

#[test]
fn an_unrecognised_proposition_refuses_and_says_which_binder() {
    // `(a b : UInt64) -> (h : a < b) -> UInt64`. `LT.lt` is proposition-shaped
    // but is not an atom this crate can restate, so the hypothesis cannot be
    // carried — and erasing it would advertise a weaker contract than the
    // kernel checked.
    let lt = Expr::apps(Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]), [
        uint64(),
        c("instLTUInt64"),
        Expr::bvar(1),
        Expr::bvar(0),
    ]);
    let ty = pi(uint64(), pi(uint64(), pi(lt, uint64())));

    let err = carrier_signature_with_hypotheses_for(&ty)
        .expect_err("a hypothesis that cannot be stated must not be erased");
    let CarrierRefused::UnrecognisedHypothesis { binder_index, .. } = &err else {
        panic!("expected UnrecognisedHypothesis, got {err:?}");
    };
    assert_eq!(*binder_index, 2);

    // v7/D3: the refusal carries the fix, WITH OPTIONS, and names the form that
    // does work — otherwise "unsupported" is the whole message.
    let note = err.to_string();
    assert!(note.contains('≠'), "the note must name the supported form:\n{note}");
    assert!(note.contains("options:"), "a refusal with no next step is a defect:\n{note}");
    assert!(
        note.matches(") ").count() >= 2,
        "a refusal with exactly one escape is an ultimatum:\n{note}"
    );
}

#[test]
fn a_hypothesis_over_another_hypothesis_refuses() {
    // `(b : UInt64) -> (h1 : b ≠ 0) -> (h2 : h1 ≠ 0) -> UInt64`. `h1` is
    // erased, so there is nothing at a call site to substitute into `h2`.
    let ty = pi(
        uint64(),
        pi(ne(Expr::bvar(0), numeral(0)), pi(ne(Expr::bvar(0), numeral(0)), uint64())),
    );
    let err = carrier_signature_with_hypotheses_for(&ty)
        .expect_err("a precondition over an erased proof cannot be discharged");
    // Two independent guards would each refuse this, and the OUTER one wins
    // because it is checked first: `h1`'s remainder mentions `h1`, so the
    // "nothing downstream depends on the proof" condition fires at binder 1
    // before `h2` is ever read. Both answers are refusals; the one recorded
    // here is the one this shape actually gets. (The recogniser's own
    // proof-operand refusal is unit-tested in `hypothesis::tests`.)
    let CarrierRefused::DependentFunctionType { binder_index, .. } = &err else {
        panic!("expected the downstream-proof-dependency refusal, got {err:?}");
    };
    assert_eq!(*binder_index, 1);
}

#[test]
fn an_ordinary_uncarried_argument_keeps_its_ordinary_refusal() {
    // `Int -> UInt8`. `Int` is not proposition-shaped and has no carrier, so
    // the new door must report the SAME positional refusal the old one does —
    // the lift changes which refusals EXIST, never which refusal a
    // non-hypothesis type gets. (`Nat` would be the wrong probe here: I6 gave
    // it the bignum carrier, so `Nat -> UInt8` is a GRANT on both doors.)
    let ty = Expr::arrow(c("Int"), c("UInt8"));
    let err = carrier_signature_with_hypotheses_for(&ty).expect_err("Int has no carrier");
    let CarrierRefused::SignatureComponent { position, cause, .. } = &err else {
        panic!("expected a positional refusal, got {err:?}");
    };
    assert_eq!(*position, trust_clean_carrier::SignaturePosition::Argument(0));

    // …and it is the base lane's own refusal, unmodified — the property
    // `the_positional_refusal_carries_the_base_refusal_unmodified` pins for the
    // old door, restated for the new one.
    let base = trust_clean_carrier::carrier_for(&c("Int")).expect_err("Int has no carrier");
    assert_eq!(format!("{cause:?}"), format!("{base:?}"));
}

#[test]
fn a_hypothesis_at_an_unbounded_type_refuses_rather_than_picking_a_width() {
    // `(n : Nat) -> (h : n ≠ 0) -> UInt64`. `Nat` has no width to state the
    // obligation at — and `Nat` in an argument has no fixed-width carrier
    // either, so this refuses twice over. Either refusal is correct; what must
    // NOT happen is a grant.
    let ne_nat = Expr::apps(Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]), [
        c("Nat"),
        Expr::bvar(0),
        Expr::app(c("Nat.zero"), Expr::nat_lit(0)),
    ]);
    let ty = pi(c("Nat"), pi(ne_nat, uint64()));
    assert!(carrier_signature_with_hypotheses_for(&ty).is_err());
}
