//@ trust-ladder: verifies
//@ trust-ladder-row: Trust verification advisory for `w14_macro2_opens_a_private_supertrait_seal::f`: 1 instance hypothesis row(s)
//! DEP-SEAL-1, macros-2.0 residual (2026-10-05): the classic sealed-trait idiom is
//! NOT a seal when the crate exports a def-site-hygienic macro that names the
//! private supertrait. `pub macro seal($t:ty) { impl private::Sealed for $t {} }`
//! resolves `private::Sealed` at its definition site, with that site's privacy, so a
//! downstream crate writes `a::seal!(Bad); impl a::T for Bad { … }`. The impl set of
//! `T` is open, and `f` must keep its obligation: with OD-1 it is an
//! `assumption:instance-hypothesis` row, CONDITIONAL under this ladder's flags, so
//! the row records `verifies` and demands that hypothesis warning, which a trait the
//! verifier still calls `Sealed` never mints.
//!
//! BEFORE (the stage 1 of `76a6ea45b2`, `scratchpad/stage1-w14`, measured
//! 2026-10-05): rc=0 under this ladder's flags with `TRUST_RUNG2_PROBE=1` printing
//! `trait=T sealedness=Sealed` and no hypothesis row, so the ladder reports the
//! needle missing; rc=0 under `-Ztrust-verify=on -Ztrust-policy=certify`. Built
//! `--crate-name a` under certify, a verify-off binary with `struct Bad;
//! a::seal!(Bad); impl a::T for Bad { fn m(&self) -> u32 { panic!() } }` printed
//! `f(&Good) = 7` and then panicked inside the certified `a::f` (exit 101; the
//! reviewer's probe `review-w14-seal/m1`, repeated).
//!
//! AFTER (the stage 1 built from this change on `40d62538d9`, measured 2026-10-05):
//! `crate_defines_def_site_macro` drops the language-visibility routes,
//! `TRUST_RUNG2_PROBE=1` prints `sealedness=Open`, and the ladder finds the needle;
//! certify exits 1 (`Trust certify verification failed for `a::f`: 1 instance
//! hypothesis row(s)`), and so does the Φ twin (rung 1). The compiletest twin is
//! `tests/ui/trust/def_site_macro_opens_a_language_visibility_seal.rs`.
#![feature(decl_macro)]
mod private {
    pub trait Sealed {}
    impl Sealed for super::Good {}
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
/// A def-site-hygienic macro that lets a downstream crate seal its own type.
pub macro seal($t:ty) {
    impl private::Sealed for $t {}
}
