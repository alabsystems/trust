//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 item 18 (shape 2): a trait-object ARGUMENT (not the receiver) of an open
//! dispatch, when THIS BODY builds it: serde-derive's
//! `<__A::Error as de::Error>::invalid_length(0, &"struct X with 2 elements")` and
//! `invalid_value(.., &"variant index 0 <= i < 2")`. The argument's type is
//! `&dyn Expected`, which the shape walk cannot see through (refused: "a `&` whose
//! pointee holds a raw pointer or an opaque part"). The operand is a local whose ONLY
//! definition is an unsizing coercion of a value the body names
//! (`_11 = copy _12 as &dyn Expected (PointerCoercion(Unsize))`), so the data pointer
//! the callee receives IS that `&C` and the vtable is `C`'s, chosen by this body's
//! own types: everything the callee can write through the fat pointer it could write
//! through `&C`. The site is now decided on the SOURCE's shape, and only an `Inert`
//! decision is taken (the bridge cannot store through a `dyn` pointee, so a source
//! that would need a havoc stays refused).
//!
//! Admitted: `missing` (`&&str`), `missing_local` (`&u32`), `generic_source`
//! (`&T`, the body's own parameter: the same inert rule as passing `&T` directly).
//! Discharge: `use_fine` (`proved`, counted skipped), `use_boom` (`Boom::invalid_length`
//! panics: `failed`).
//! Controls that stay refused (class (c) `failed`): `forwarded` (the caller's trait
//! object: no unsizing here), `cell_object` (`&Cell<u32>` unsized: interior
//! mutability needs a havoc the bridge cannot do through `dyn`), `mut_object`
//! (`&mut u32` unsized into `&mut dyn`), `reseated` and `reseated_to_local` (two definitions of the operand, in
//! either order: the caller's trait object reaches the call on one path).
use std::cell::Cell;

pub trait Expected {
    fn show(&self) -> usize;
}

impl Expected for &str {
    fn show(&self) -> usize {
        self.len()
    }
}

impl Expected for u32 {
    fn show(&self) -> usize {
        1
    }
}

impl Expected for Cell<u32> {
    fn show(&self) -> usize {
        self.set(0);
        2
    }
}

pub trait Error: Sized {
    fn invalid_length(len: usize, exp: &dyn Expected) -> Self;
}

pub fn missing<E: Error>() -> E {
    //[advisory]~^ WARN Trust verification advisory for `dyn_argument_built_here_admitted::missing`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `dyn_argument_built_here_admitted::missing`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `dyn_argument_built_here_admitted::missing`: 1 instance hypothesis row(s)
    E::invalid_length(0, &"struct with 1 element")
}

pub fn missing_local<E: Error>(n: u32) -> E {
    //[advisory]~^ WARN Trust verification advisory for `dyn_argument_built_here_admitted::missing_local`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `dyn_argument_built_here_admitted::missing_local`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `dyn_argument_built_here_admitted::missing_local`: 1 instance hypothesis row(s)
    let k = n;
    E::invalid_length(1, &k)
}

pub fn generic_source<E: Error, T: Expected>(t: &T) -> E {
    //[advisory]~^ WARN Trust verification advisory for `dyn_argument_built_here_admitted::generic_source`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `dyn_argument_built_here_admitted::generic_source`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `dyn_argument_built_here_admitted::generic_source`: 1 instance hypothesis row(s)
    E::invalid_length(2, t)
}

pub struct Fine;
pub struct Boom;

impl Error for Fine {
    fn invalid_length(_len: usize, _exp: &dyn Expected) -> Self {
        Fine
    }
}

impl Error for Boom {
    fn invalid_length(_len: usize, _exp: &dyn Expected) -> Self {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `<dyn_argument_built_here_admitted::Boom as dyn_argument_built_here_admitted::Error>::invalid_length`: 2 obligation(s) were not proved
        //[strict]~^^ ERROR Trust strict verification failed for `<dyn_argument_built_here_admitted::Boom as dyn_argument_built_here_admitted::Error>::invalid_length`: 2 obligation(s) were not fully verified
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `<dyn_argument_built_here_admitted::Boom as dyn_argument_built_here_admitted::Error>::invalid_length`: 2 obligation(s) were not proved
        //[certify]~^^^^ ERROR Trust strict verification failed for `<dyn_argument_built_here_admitted::Boom as dyn_argument_built_here_admitted::Error>::invalid_length`: 2 obligation(s) were not fully verified
        panic!("boom")
    }
}

pub fn use_fine() -> Fine {
    //[certify]~^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::use_fine`: 1 obligation(s) were not proved
    //[certify]~^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::use_fine`: 1 obligation(s) were not fully verified
    missing::<Fine>()
}

pub fn use_boom() -> Boom {
    //[advisory]~^ WARN Trust instance discharge not established for `dyn_argument_built_here_admitted::use_boom`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `dyn_argument_built_here_admitted::use_boom`: 1 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::use_boom`: 1 obligation(s) were not fully verified
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::use_boom`: 1 obligation(s) were not proved
    //[certify]~^^^^^ ERROR Trust instance discharge not established for `dyn_argument_built_here_admitted::use_boom`: 1 instance(s)
    //[certify]~^^^^^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::use_boom`: 1 obligation(s) were not fully verified
    missing::<Boom>()
}

// Controls: still refused.

pub fn forwarded<E: Error>(exp: &dyn Expected) -> E {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::forwarded`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::forwarded`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::forwarded`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::forwarded`: 1 obligation(s) were not fully verified
    E::invalid_length(0, exp)
}

pub fn cell_object<E: Error>(c: &Cell<u32>) -> E {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::cell_object`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::cell_object`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::cell_object`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::cell_object`: 1 obligation(s) were not fully verified
    E::invalid_length(0, c)
}

pub trait MutError: Sized {
    fn poke(len: usize, exp: &mut dyn Expected) -> Self;
}

pub fn mut_object<E: MutError>() -> E {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::mut_object`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::mut_object`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::mut_object`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::mut_object`: 1 obligation(s) were not fully verified
    let mut k = 3u32;
    E::poke(0, &mut k)
}

pub fn reseated<E: Error>(b: bool, exp: &dyn Expected) -> E {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::reseated`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::reseated`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::reseated`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::reseated`: 1 obligation(s) were not fully verified
    let mut d: &dyn Expected = &"x";
    if b {
        d = exp;
    }
    E::invalid_length(0, d)
}

pub fn reseated_to_local<E: Error>(b: bool, exp: &dyn Expected) -> E {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::reseated_to_local`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::reseated_to_local`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `dyn_argument_built_here_admitted::reseated_to_local`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `dyn_argument_built_here_admitted::reseated_to_local`: 1 obligation(s) were not fully verified
    let mut d: &dyn Expected = exp;
    if b {
        d = &"x";
    }
    E::invalid_length(0, d)
}
