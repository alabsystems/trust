// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! CONTROL (d) — THE FUNCTION-TYPED CARRIER.
//!
//! I4 decided base types. A Clean `def` has a **`Pi`** for a type, so until a
//! function type has a carrier no Clean function can be minted at all — I5's own
//! parity fixture, `def f (a : UInt64) : UInt64 := a`, has kernel type
//! `UInt64 -> UInt64`.
//!
//! The whole risk of this increment is that a *signature* carrier becomes the
//! hole the base-type discipline was built to close. So the controls here are
//! not "does the arrow work"; they are **the I4 properties, restated
//! positionally**:
//!
//! * total on its domain — one unmodeled component and the SIGNATURE has none;
//! * `Int` anywhere refuses, exactly as it does alone (the "assume in range"
//!   trap, now with somewhere to hide). `Nat` flipped to a GRANT at I6 — at
//!   the exact bignum carrier `trust_bignum::Nat` only, never at a width —
//!   so the poisoned-signature properties are pinned on `Int` here;
//! * `Prop` anywhere refuses — it is not a value in any position;
//! * a witness for a signature exists only when every component is witnessed;
//! * a genuinely dependent `Pi` has no Rust signature and is refused rather
//!   than having its dependency erased.

use clean_kernel::{BinderInfo, Expr, Name};
use trust_clean_carrier::{
    carrier_for, carrier_signature_for, CarrierRefused, CleanType, SignaturePosition,
};
use trust_symbols::{CarrierEvidence, CarrierWitness};
use trust_types::Ty;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

// ---------------------------------------------------------------------------
// 1. The positive: the parity fixture's own type
// ---------------------------------------------------------------------------

#[test]
fn the_parity_fixture_type_uint64_to_uint64_gets_a_signature_carrier() {
    // `def f (a : UInt64) : UInt64 := a` — kernel type `UInt64 -> UInt64`.
    let sig = carrier_signature_for(&Expr::arrow(c("UInt64"), c("UInt64")))
        .expect("UInt64 -> UInt64 is exact in every position; it must be granted");

    assert_eq!(sig.arity(), 1);
    assert_eq!(sig.arguments().len(), 1);
    assert_eq!(sig.arguments()[0].clean(), CleanType::UInt(64));
    assert_eq!(*sig.arguments()[0].rust(), u64_ty());
    assert_eq!(sig.result().clean(), CleanType::UInt(64));
    assert_eq!(*sig.result().rust(), u64_ty());
    assert_eq!(sig.evidence(), CarrierEvidence::Total);
}

// ---------------------------------------------------------------------------
// 2. Arity 0 and arity 2+
// ---------------------------------------------------------------------------

#[test]
fn a_bare_type_is_arity_zero_and_agrees_with_the_base_carrier() {
    let sig = carrier_signature_for(&c("UInt64")).expect("a bare UInt64 is a nullary signature");
    assert_eq!(sig.arity(), 0);
    assert!(sig.arguments().is_empty());
    assert_eq!(sig.result().clean(), CleanType::UInt(64));

    // The nullary case is not a second decision procedure: it is the base
    // carrier, reused.
    let base = carrier_for(&c("UInt64")).expect("UInt64 has a base carrier");
    assert_eq!(sig.result(), &base);
}

#[test]
fn arity_two_composes_the_base_decisions_positionally() {
    // UInt64 -> Bool -> UInt32
    let ty = Expr::arrow(c("UInt64"), Expr::arrow(c("Bool"), c("UInt32")));
    let sig = carrier_signature_for(&ty).expect("every position is exact");

    assert_eq!(sig.arity(), 2);
    assert_eq!(*sig.arguments()[0].rust(), u64_ty());
    assert_eq!(*sig.arguments()[1].rust(), Ty::Bool);
    assert_eq!(*sig.result().rust(), Ty::Int { width: 32, signed: false });
    assert_eq!(sig.evidence(), CarrierEvidence::Total);
}

// ---------------------------------------------------------------------------
// 3. One bad component poisons the whole signature — and the refusal says WHICH
// ---------------------------------------------------------------------------

#[test]
fn an_int_argument_refuses_the_whole_signature_and_names_the_argument() {
    // Re-pinned from `Nat` at I6 (which now grants — see
    // `nat_positions_grant_at_the_bignum_carrier_but_int_does_not`): `Int` is
    // unbounded with NO carrier, so it pins the poisoned-signature property.
    let err = carrier_signature_for(&Expr::arrow(c("Int"), c("UInt64")))
        .expect_err("`Int` is uncarried in argument position exactly as it is alone");

    let CarrierRefused::SignatureComponent { position, cause, .. } = &err else {
        panic!("expected a positional refusal, got {err:?}");
    };
    assert_eq!(*position, SignaturePosition::Argument(0));
    // The SAME refusal the base type gets — not a softer one.
    assert!(matches!(**cause, CarrierRefused::Narrowing { .. }), "{cause:?}");

    let text = err.to_string();
    assert!(text.contains("argument 0"), "names the position: {text}");
    assert!(text.contains("options:"), "carries the fix (v7/D3): {text}");
}

#[test]
fn an_int_result_refuses_the_whole_signature_and_names_the_result() {
    let err = carrier_signature_for(&Expr::arrow(c("UInt64"), c("Int")))
        .expect_err("an `Int` result is uncarried, whatever the arguments are");

    let CarrierRefused::SignatureComponent { position, cause, .. } = &err else {
        panic!("expected a positional refusal, got {err:?}");
    };
    assert_eq!(*position, SignaturePosition::Result);
    assert!(matches!(**cause, CarrierRefused::Narrowing { .. }), "{cause:?}");

    let text = err.to_string();
    assert!(text.contains("the result"), "names the position: {text}");
    assert!(text.contains("options:"), "{text}");
}

#[test]
fn no_partial_credit_the_good_arguments_do_not_rescue_the_bad_one() {
    // Three of the four positions are exact. That earns nothing.
    let ty = Expr::arrow(
        c("UInt64"),
        Expr::arrow(c("Bool"), Expr::arrow(c("Int"), c("UInt32"))),
    );
    let err = carrier_signature_for(&ty).expect_err("one uncarried component sinks the signature");
    let CarrierRefused::SignatureComponent { position, .. } = &err else {
        panic!("expected a positional refusal, got {err:?}");
    };
    assert_eq!(*position, SignaturePosition::Argument(2));
}

/// The I6 flip, stated positively AND with its boundary: `Nat` positions carry
/// (at the exact bignum type), `Int` positions do not — in the same file that
/// pins the refusals, so the two can never drift apart unnoticed.
#[test]
fn nat_positions_grant_at_the_bignum_carrier_but_int_does_not() {
    let sig = carrier_signature_for(&Expr::arrow(c("Nat"), c("UInt64")))
        .expect("I6: a Nat argument carries at trust_bignum::Nat");
    assert_eq!(*sig.arguments()[0].rust(), Ty::BignumNat);
    assert_eq!(*sig.result().rust(), u64_ty());

    let sig = carrier_signature_for(&Expr::arrow(c("UInt64"), c("Nat")))
        .expect("I6: a Nat result carries at trust_bignum::Nat");
    assert_eq!(*sig.result().rust(), Ty::BignumNat);

    assert!(carrier_signature_for(&Expr::arrow(c("Int"), c("Bool"))).is_err());
}

#[test]
fn a_known_value_never_turns_a_positional_refusal_into_a_grant() {
    // The I4 property, restated positionally: an uncarried type does not
    // become carryable by being in a position somebody considers
    // uninteresting. (`Nat` left this list at I6 — it is genuinely carried
    // now, in every position, at the exact bignum type.)
    for ty in [
        Expr::arrow(c("Int"), c("UInt64")),
        Expr::arrow(c("UInt64"), c("Int")),
        Expr::arrow(c("Int"), c("Bool")),
        Expr::arrow(c("USize"), c("UInt64")),
        Expr::arrow(c("UInt64"), c("USize")),
        Expr::arrow(c("MyAlias"), c("UInt64")),
        Expr::arrow(c("UInt64"), c("Float")),
    ] {
        assert!(
            carrier_signature_for(&ty).is_err(),
            "a signature is granted only when EVERY component is: {ty:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// 4. `Prop` anywhere refuses
// ---------------------------------------------------------------------------

#[test]
fn prop_in_any_position_refuses_because_it_is_not_a_value() {
    for (ty, expected) in [
        (Expr::arrow(c("Prop"), c("UInt64")), SignaturePosition::Argument(0)),
        (Expr::arrow(c("UInt64"), c("Prop")), SignaturePosition::Result),
        (
            Expr::arrow(c("UInt64"), Expr::arrow(c("Prop"), c("Bool"))),
            SignaturePosition::Argument(1),
        ),
    ] {
        let err = carrier_signature_for(&ty).expect_err("a Prop is observed, never produced");
        let CarrierRefused::SignatureComponent { position, cause, .. } = &err else {
            panic!("expected a positional refusal, got {err:?}");
        };
        assert_eq!(*position, expected);
        assert!(matches!(**cause, CarrierRefused::NotAValue { .. }), "{cause:?}");
    }

    // And a `Sort` spelled as a sort, not as the constant `Prop`.
    let sort = Expr::prop();
    assert!(carrier_signature_for(&Expr::arrow(sort, c("UInt64"))).is_err());
}

// ---------------------------------------------------------------------------
// 5. The witness is total or absent
// ---------------------------------------------------------------------------

#[test]
fn a_signature_carrier_is_witnessed_in_every_position_or_it_does_not_exist() {
    let ty = Expr::arrow(c("UInt8"), Expr::arrow(c("Bool"), c("UInt32")));
    let sig = carrier_signature_for(&ty).expect("all exact");

    // Every component holds a real `CarrierWitness` — the `Ok` of
    // `RepresentationObligation::discharge`, which is the only way one exists.
    let witnesses: Vec<&CarrierWitness> = sig.witnesses().collect();
    assert_eq!(witnesses.len(), sig.arity() + 1, "one witness per position, including the result");
    assert_eq!(witnesses[0].clean_type(), "UInt8");
    assert_eq!(witnesses[0].rust_carrier(), "u8");
    assert_eq!(witnesses[1].clean_type(), "Bool");
    assert_eq!(witnesses[2].clean_type(), "UInt32");
    assert_eq!(witnesses[2].width(), trust_symbols::CarrierWidth::Bits(32));

    assert_eq!(sig.evidence(), CarrierEvidence::Total);
}

#[test]
fn the_result_witness_is_what_a_symbol_header_records() {
    use trust_symbols::{Producer, SegmentPath, Sort, SymbolHeader};

    let sig = carrier_signature_for(&Expr::arrow(c("UInt64"), c("UInt32")))
        .expect("UInt64 -> UInt32 is exact in both positions");
    let header = SymbolHeader::new(
        SegmentPath::parse_rust("crate::f").expect("valid path"),
        Sort::Term,
        Producer::Clean,
    );
    let recorded = sig.record_result_on(header);
    assert_eq!(recorded.carrier(), CarrierEvidence::Total);
    // The value the CALL produces is the result, not the argument.
    assert_eq!(
        recorded.carrier_witness().map(CarrierWitness::width),
        Some(trust_symbols::CarrierWidth::Bits(32))
    );
}

// ---------------------------------------------------------------------------
// 6. A dependent `Pi` refuses rather than having its dependency erased
// ---------------------------------------------------------------------------

#[test]
fn a_genuinely_dependent_pi_is_refused_not_flattened() {
    // (a : UInt64) -> Vec a  — the binder is USED. There is no Rust signature
    // for this, so it is refused rather than erased down to `UInt64 -> Vec`.
    let dependent = Expr::pi(BinderInfo::Default, c("UInt64"), Expr::app(c("Vec"), Expr::bvar(0)));
    let err = carrier_signature_for(&dependent).expect_err("the dependency must not be erased");
    assert!(matches!(err, CarrierRefused::DependentFunctionType { .. }), "{err:?}");
    let text = err.to_string();
    assert!(text.contains("options:"), "{text}");
}

#[test]
fn dependency_is_detected_at_the_binder_that_is_actually_used() {
    // (a : UInt64) -> (b : Bool) -> P a  — argument 0's binder is used from two
    // levels down, which is exactly the case a shallow "does the body mention
    // bvar 0" check would miss.
    let inner = Expr::pi(BinderInfo::Default, c("Bool"), Expr::app(c("P"), Expr::bvar(1)));
    let dependent = Expr::pi(BinderInfo::Default, c("UInt64"), inner);
    let err = carrier_signature_for(&dependent).expect_err("argument 0 is depended on");
    let CarrierRefused::DependentFunctionType { binder_index, .. } = &err else {
        panic!("expected a dependency refusal, got {err:?}");
    };
    assert_eq!(*binder_index, 0);
}

#[test]
fn a_non_dependent_pi_written_with_an_explicit_binder_is_still_granted() {
    // Same constructor as the dependent case; the binder is simply not used.
    // The test is that the dependency check keys on USE, not on the binder
    // being named.
    let ty = Expr::pi(BinderInfo::Default, c("UInt64"), c("Bool"));
    let sig = carrier_signature_for(&ty).expect("the binder is unused, so this is an arrow");
    assert_eq!(sig.arity(), 1);
    assert_eq!(*sig.result().rust(), Ty::Bool);
}

// ---------------------------------------------------------------------------
// Fail-closed on shapes nobody modeled
// ---------------------------------------------------------------------------

#[test]
fn a_higher_order_argument_gets_no_carrier() {
    // (UInt64 -> UInt64) -> UInt64. Every leaf is exact; the ARGUMENT is a
    // function, and there is no carrier for a function VALUE.
    let ty = Expr::arrow(Expr::arrow(c("UInt64"), c("UInt64")), c("UInt64"));
    let err = carrier_signature_for(&ty).expect_err("a function argument is not a carried value");
    let CarrierRefused::SignatureComponent { position, cause, .. } = &err else {
        panic!("expected a positional refusal, got {err:?}");
    };
    assert_eq!(*position, SignaturePosition::Argument(0));
    assert!(matches!(**cause, CarrierRefused::UnmodeledCleanType { .. }), "{cause:?}");
}

#[test]
fn the_base_lane_still_refuses_a_pi_so_nothing_widened_underneath() {
    // `carrier_for` is unchanged: a function type is not a base carrier, and
    // the signature lane is an ADDITION rather than a loosening.
    assert!(carrier_for(&Expr::arrow(c("UInt64"), c("UInt64"))).is_err());
}
