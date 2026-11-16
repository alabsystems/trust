//~ NOTE "function":"uninhabited_argument_function_publishes_one_envelope::void_and_more"
//~| NOTE "function":"<uninhabited_argument_function_publishes_one_envelope::MyError as core::convert::From<!>>::from"
//~| NOTE "function":"<uninhabited_argument_function_publishes_one_envelope::Impossible<Ok> as uninhabited_argument_function_publishes_one_envelope::End>::end"
//~| NOTE "type":"coverage_summary","crate_name":"uninhabited_argument_function_publishes_one_envelope","package_name":"","primary_package":false,"verification_session":"","eligible":3,"processed":3,
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Trust (2026-10-17, coverage identity): a body with a BY-VALUE argument of an
//! uninhabited type is declined as `UninhabitedArgument` (it can never be entered),
//! and it is still a coverage-eligible body the pass credits as processed. targo
//! authenticates the processed identities against the function envelopes as an
//! EXACT set, so the body must publish one envelope: the zero-obligation inventory
//! row, as the lone-`unreachable` early-out does. Lines 1-3 pin one `function_result`
//! envelope per uncallable body and line 4 the coverage row that credits all three
//! (compiletest reads the span-less `TRUST_JSON:` transport notes at line 1). Since
//! 1.101 `Infallible` is `!` (`pub type Infallible = !`), so the `From` impl's def
//! path renders `From<!>`.
//!
//! Before: the bodies were credited and published nothing (MEASURED with the
//! 2026-10-16 candidate trustc 7f3690ed73 on this file: `eligible`/`processed` 3 and
//! no `function_result` envelope at all), so strict `targo trust` refused such a crate
//! ("processed coverage identities did not exactly equal authenticated function
//! envelopes") and advisory reported `Coverage: unknown`. aterm-serde's seven
//! `Impossible::end(self)` bodies took that path on the candidate gate.
use std::convert::Infallible;
use std::marker::PhantomData;

pub enum Void {}

pub enum MyError {
    Bad,
}

impl From<Infallible> for MyError {
    fn from(x: Infallible) -> Self {
        match x {}
    }
}

pub fn void_and_more(v: Void, y: u8) -> u8 {
    let _ = y;
    match v {}
}

pub struct Impossible<Ok> {
    void: Void,
    ok: PhantomData<Ok>,
}

pub trait End {
    type Ok;
    fn end(self) -> Self::Ok;
}

impl<Ok> End for Impossible<Ok> {
    type Ok = Ok;
    fn end(self) -> Ok {
        match self.void {}
    }
}

