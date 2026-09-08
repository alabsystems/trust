//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-TSD): the wave-DA/wave-MR SEALED-DIVERGENCE arm was present at
//! three call sites (`Repeat` element, `lower_call_args`, `Return`) and simply
//! absent from the tuple field loop.
//!
//! When a tuple field's own lowering emits the terminator, the aggregate is
//! DEAD CODE — rustc evaluates tuple operands left to right and the aggregate
//! block is unreachable, so built MIR agrees. No tag, no value.
//!
//! A field that pushed its OWN tag before diverging keeps it and still fails
//! closed, so the partially-refused-then-diverged corner is untouched.

// Trust: the `1u32` after a diverging `loop {}` is unreachable by construction;
// the warning is incidental to what this test pins, and an unannotated WARN
// fails a `run-pass` for every session.
#![allow(unreachable_code)]

pub fn diverging_tuple_field(go: bool) -> u32 {
    if go {
        return 7;
    }
    let _t = (loop {}, 1u32);
}

fn main() {
    assert_eq!(diverging_tuple_field(true), 7);
}
