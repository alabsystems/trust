//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `summary_generic_impl_call_key_alias.rs` (SUMMARY-NAME-COLLIDE-1,
//! the call-site half): the `inherent` whose `[overflow:add]` that file's BEFORE
//! compiler proved, kernel-certified under certify, from the CONCRETE sibling
//! impl's const-set summary `{1}`. The call names the concrete sibling's key but
//! runs the GENERIC impl's `get`, which returns its argument, so
//! `inherent(u32::MAX)` overflows.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it
//! pins that the call really overflows, not the verdict. The BEFORE compiler did
//! not elide the check either (a verify-off binary linked against its certify
//! rlib panicked the same way; review measurement on the stage 1 of `dc15b882f6`).
//! Measured 2026-10-05 on that stage 1 (`scratchpad/stage1-w16`): built
//! `-Ztrust-verify=off` it exits 101 with the message above.

pub struct V<T>(pub T);
pub trait Marker {}
impl Marker for V<for<'a> fn(&'a u8) -> &'a u8> {}

pub struct W<T>(pub T);
impl<T: Marker> W<T> {
    pub fn get(x: u32) -> u32 {
        x
    }
}
impl W<V<for<'a> fn(&'a u8) -> &'static u8>> {
    pub fn get(_x: u32) -> u32 {
        1
    }
}

#[inline(never)]
pub fn inherent(x: u32) -> u32 {
    let y = W::<V<for<'a> fn(&'a u8) -> &'a u8>>::get(x);
    y + 1
}

fn main() {
    println!("{}", inherent(std::hint::black_box(u32::MAX)));
}
