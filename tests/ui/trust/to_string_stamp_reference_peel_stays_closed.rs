//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! THE BOUNDARY OF THE `ToString::to_string` TOTALITY STAMP, as a check that can
//! FAIL.
//!
//! The stamp's audit is a list of `SpecToString` impls read from
//! `library/alloc/src/string.rs` in this tree. That list is:
//!
//! ```text
//! core::ascii::Char | char | bool | every iN/uN          (BARE)
//! Cow<'_, str> | String | str | &str | … | &&&&&&&&&&&&str  (to_string_str!)
//! fmt::Arguments<'_>
//! ```
//!
//! and every OTHER `Self` selects the blanket default, whose body ends in
//! `.expect("a Display implementation returned an error unexpectedly")`.
//!
//! The first revision of the stamp peeled `&` off ANY base and then accepted
//! `Bool`/`Char`/`Int`/`Uint`/`String` underneath, so it admitted `&u32`,
//! `&&bool` and `&String` — three types with NO `SpecToString` impl. The audit
//! that justified the stamp therefore did not cover the set the code accepted:
//! the model was asserting totality of a body it had never read. (These three
//! happen to be total in fact, which is exactly why the gap was invisible; a
//! model is an axiom, and an axiom nobody checked is the hazard whether or not
//! today's instance is benign.)
//!
//! The peel is now confined to the `str` chain: `&`-peeling happens only when
//! the chain terminates at `TyKind::Str`, within the twelve references
//! `to_string_str!` actually lists, and every other admitted `Self` must be
//! BARE.
//!
//! Each function below therefore keeps an honest may-panic obligation. Under
//! `-Ztrust-policy=certify` an unproved obligation is an error, which is what
//! makes this fixture able to refute: if the peel is ever widened again, these
//! rows go green and the file stops failing.
//!
//! `ToString::to_string(&x)` rather than `x.to_string()` is deliberate —
//! method-call autoderef would resolve `x.to_string()` to the BARE primitive and
//! measure nothing.

/// `&u32`: no `SpecToString for &u32`. Selects the blanket default.
pub fn peel_ref_u32(x: &u32) -> String {
    //~^ ERROR Trust Level 0 safety verification incomplete for `to_string_stamp_reference_peel_stays_closed::peel_ref_u32`
    //~| ERROR Trust strict verification failed for `to_string_stamp_reference_peel_stays_closed::peel_ref_u32`
    ToString::to_string(&x)
}

/// `&&bool`: the `bool` specialization is written for the BARE primitive.
pub fn peel_ref_ref_bool(b: &&bool) -> String {
    //~^ ERROR Trust Level 0 safety verification incomplete for `to_string_stamp_reference_peel_stays_closed::peel_ref_ref_bool`
    //~| ERROR Trust strict verification failed for `to_string_stamp_reference_peel_stays_closed::peel_ref_ref_bool`
    ToString::to_string(&b)
}

/// `&String`: `to_string_str!` lists `String` and the `str` chain. Not `&String`.
pub fn peel_ref_string(s: &String) -> String {
    //~^ ERROR Trust Level 0 safety verification incomplete for `to_string_stamp_reference_peel_stays_closed::peel_ref_string`
    //~| ERROR Trust strict verification failed for `to_string_stamp_reference_peel_stays_closed::peel_ref_string`
    ToString::to_string(&s)
}
