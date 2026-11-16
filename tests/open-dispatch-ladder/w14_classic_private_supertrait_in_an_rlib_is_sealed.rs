//@ trust-ladder: verifies
//! THE CONTROL for the `w14_*_stays_refused` rows (DEP-SEAL-1): the classic
//! sealed-trait idiom keeps its seal in an rlib. `Sealed` is not exported and is
//! implemented only for concrete types, and `T` has no type parameter, so no
//! downstream crate can write an impl of `T` that type-checks.
//!
//! `impl<'a> Sealed for &'a Good` is here on purpose: rule (c) of
//! `private_supertrait_seals` refuses a type or const parameter in a supertrait
//! impl's self type, never a lifetime. `&'a Good` contains no downstream type, and
//! `&` of a foreign type is not local downstream.
//!
//! BEFORE, measured 2026-10-04 on this file with the wave-14 scout's `stage1-w12`:
//! rc=0 under this ladder's flags (`TRUST_RUNG2_PROBE=1`: `sealedness=Sealed`), and
//! rc=0 under `-Ztrust-verify=on -Ztrust-policy=certify`. Built `--crate-name a`
//! under certify, a downstream `impl a::T for Bad` is rejected with E0277 (`Bad:
//! a::private::Sealed` is not satisfied), and `impl<'a> a::T for &'a a::Good` with
//! E0117 (the orphan rule).
//!
//! AFTER (predicted, not built): rc=0; rules (a)–(d) all hold. If this row goes
//! red, the fix over-refused the idiom it exists to keep.
mod private {
    pub trait Sealed {}
    impl Sealed for super::Good {}
    impl<'a> Sealed for &'a super::Good {}
}
pub trait T: private::Sealed {
    fn m(&self) -> u32;
}
pub struct Good;
impl T for Good {
    fn m(&self) -> u32 {
        7
    }
}
pub fn f<K: T>(x: &K) -> u32 {
    x.m()
}
