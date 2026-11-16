//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for `loop_trip_zero_factor_is_not_a_bound.rs`
//! (TRIP-ZERO-PRODUCT-1): a zero-trip warm-up loop must not cancel the 300-trip
//! loop's factor, so the `c += 1` overflow check survives and the 256th add panics
//! exactly as vanilla Rust does.
//!
//! BEFORE (`scratchpad/stage1-w12`, this file's flags, measured 2026-10-04): the
//! build exited 0 with no warning; `count_after_warmup`'s add was
//! kernel-certified under the false fact `c <= 0` (`K=0`), its check was elided, and
//! the program printed `44` and exited 0. The `count_after_warmup` warning below was
//! missing and the error pattern never appeared.
//!
//! AFTER (predicted, not built): `K = 300`, the add is a refuted overflow (a warning
//! under advisory), nothing is elided, and the program panics with `attempt to add
//! with overflow`. Derived on the same stage 1 from a line-for-line twin with
//! `WARMUP = 1` (the factor the clamp gives): it built with exactly the one warning
//! annotated here, and its binary panicked with that message, exit 101.

const WARMUP: u32 = 0;

fn count_after_warmup() -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete
    let mut c: u8 = 0;
    for _ in 0..WARMUP {}
    for _ in 0..300u32 {
        c += 1;
    }
    c
}

fn main() {
    println!("{}", count_after_warmup());
}
