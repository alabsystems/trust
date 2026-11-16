//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `generic_call_key_alias_blanket_impl.rs`
//! (GENERIC-CALL-KEY-ALIAS-1): the `certify_ovf` shape, whose `[overflow:add]`
//! the BEFORE compiler proved and kernel-certified under certify. It used the
//! blanket impl's bound `m() == 1`, because the generic call printed as that
//! body's definition key. `f::<Foo>` runs Foo's own `m`, which returns
//! `u32::MAX`, so `f(&Foo)` overflows.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it
//! pins that the call really overflows, not the verdict. The BEFORE compiler
//! did not elide the check either: `f` is generic, `TRUST_ELIDE_DEBUG` showed 0
//! checks elided in it, and a verify-off consumer linked against the certify
//! rlib panicked the same way (scout probe, stage 1 of `4ccd862830`).
//! Measured 2026-10-06 on that stage 1 (`scratchpad/stage1-w18b`): built
//! `-Ztrust-verify=off -Coverflow-checks=on` (rc=0), it exits 101 with the
//! message above.
#![allow(dead_code, private_bounds)]

trait Marker {}
trait Tr {
    #[trust::panic_free]
    fn m(&self) -> u32;
}

impl<T: Marker> Tr for T {
    fn m(&self) -> u32 {
        1
    }
}

pub struct Foo;
impl Tr for Foo {
    fn m(&self) -> u32 {
        u32::MAX
    }
}

#[inline(never)]
pub fn f<T: Tr>(x: &T) -> u32 {
    x.m() + 1
}

fn main() {
    println!("{}", f(std::hint::black_box(&Foo)));
}
