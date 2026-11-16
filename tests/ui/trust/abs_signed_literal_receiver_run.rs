//@ run-fail
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: attempt to negate with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `abs_signed_literal_receiver.rs` (ABS-LIT-WIDTH-1): `i32::MIN.abs()`
//! panics "attempt to negate with overflow". Before the fix, the verifier published a
//! clean-kernel `Certified` PROVED negation row for this call (built at 64 bits), and
//! the default verify-on build of this program exited 0; its binary panicked the same
//! way (measured 2026-10-11 on a pre-fix stage 1, `scratchpad/stage1-w22probe`). This
//! file passes before and after the fix: it pins the panic the row must not deny.

#[inline(never)]
pub fn a32() -> i32 {
    i32::MIN.abs()
}

fn main() {
    println!("{}", a32());
}
