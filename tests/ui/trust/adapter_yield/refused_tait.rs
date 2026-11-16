//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! D2 tier 1: a crate that enables `type_alias_impl_trait` gets NO
//! `ADAPTER_YIELD` premise at all.
//!
//! The occurrence accounting reads only the parent's MIR. With TAIT the closure
//! type is nameable crate-wide (`P`), so another body can conjure the
//! (zero-sized) closure — `transmute::<(), P>(())` is not UB for a capture-free
//! closure — and call it on items the adapter never yielded
//! (`conjure_and_call(&[])` indexes `w[1]` of an empty slice). Found by the D2
//! adversarial review (2026-09-25, probe fp18): without this decline only the
//! conjuring body's unrelated unsafe-operation row kept the crate refused, and
//! the closure's premise WAS installed. Here there is no conjuring body at all:
//! the closure must be refused on its own bounds row, with no modeled-fact note.
#![feature(type_alias_impl_trait)]
pub type P = impl Fn(&[u32]) -> bool + Copy;

#[define_opaque(P)]
pub fn check(v: &[u32]) -> bool {
    v.windows(2).all::<P>(|w| w[1] > 0)
    //~^ ERROR Trust Level 0 safety verification incomplete for `refused_tait::check::{closure#0}`
    //~| ERROR Trust strict verification failed for `refused_tait::check::{closure#0}`
}
