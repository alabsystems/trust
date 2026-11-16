//@ trust-ladder: verifies
//@ trust-ladder-row: Trust verification advisory for `w14_macro2_opens_a_non_exported_trait::f`: 1 instance hypothesis row(s)
//! DEP-SEAL-1, macros-2.0 residual (2026-10-05), the NON-EXPORTED route: a trait no
//! `use` exports is still implementable downstream through a def-site-hygienic
//! macro of its crate. `pub macro imp($t:ty, $v:expr) { impl private::T for $t { … }
//! }` resolves `private::T` at its definition site, so a downstream crate writes
//! `a::imp!(Bad, panic!(..))` and calls `a::f(&Bad)`. The row records `verifies`
//! and demands OD-1's instance-hypothesis warning, which a trait the verifier still
//! calls `Sealed` never mints.
//!
//! BEFORE (the stage 1 of `76a6ea45b2`, `scratchpad/stage1-w14`, measured
//! 2026-10-05): rc=0 under this ladder's flags with `TRUST_RUNG2_PROBE=1` printing
//! `trait=T sealedness=Sealed` and no hypothesis row; rc=0 under
//! `-Ztrust-verify=on -Ztrust-policy=certify`. A verify-off downstream with
//! `a::imp!(Bad, panic!(..))` panicked inside the certified `a::f` (exit 101; the
//! reviewer's probe `review-w14-seal/m2`, repeated).
//!
//! AFTER (the stage 1 built from this change on `40d62538d9`, measured 2026-10-05):
//! `crate_defines_def_site_macro` drops the language-visibility routes,
//! `TRUST_RUNG2_PROBE=1` prints `sealedness=Open`, and the ladder finds the needle;
//! certify exits 1 (`Trust certify verification failed for `a::f`: 1 instance
//! hypothesis row(s)`).
#![feature(decl_macro)]
mod private {
    pub trait T {
        fn m(&self) -> u32;
    }
}
pub struct Good;
impl private::T for Good {
    fn m(&self) -> u32 {
        7
    }
}
#[allow(private_bounds)]
pub fn f<K: private::T>(x: &K) -> u32 {
    x.m()
}
/// A def-site-hygienic macro that lets a downstream crate implement the
/// non-exported trait.
pub macro imp($t:ty, $v:expr) {
    impl private::T for $t {
        fn m(&self) -> u32 {
            $v
        }
    }
}
