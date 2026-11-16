//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `summary_hrtb_impl_name_collision.rs` (SUMMARY-NAME-COLLIDE-1):
//! the `const_set` whose `[overflow:add]` that file's BEFORE compiler proved —
//! kernel-certified under certify — from the SIBLING impl's const-set summary
//! `{1}`, because both impls' `get` render one key. The impl the call runs
//! returns its argument, so `const_set(u32::MAX)` overflows.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it
//! pins that the call really overflows, not the verdict. Measured 2026-10-05 on
//! the stage 1 at `scratchpad/stage1-w14` (`76a6ea45b2`): built
//! `-Ztrust-verify=off` it exits 101 with the message above.
#![allow(coherence_leak_check)]

pub struct W<T>(pub T);

pub trait Tr {
    fn get(x: u32) -> u32;
}

impl Tr for W<for<'a> fn(&'a u8) -> &'static u8> {
    fn get(x: u32) -> u32 {
        x
    }
}

impl Tr for W<for<'a> fn(&'a u8) -> &'a u8> {
    fn get(_x: u32) -> u32 {
        1
    }
}

#[inline(never)]
pub fn const_set(x: u32) -> u32 {
    <W<for<'a> fn(&'a u8) -> &'static u8> as Tr>::get(x) + 1
}

fn main() {
    println!("{}", const_set(std::hint::black_box(u32::MAX)));
}
