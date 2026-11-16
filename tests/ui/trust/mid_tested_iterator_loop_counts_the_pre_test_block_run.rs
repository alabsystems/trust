//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for `mid_tested_loop_counts_the_pre_test_block.rs`
//! (TRIP-MID-TEST-1), iterator lane: the `next()` driver is not the loop's header,
//! `c += 1` runs before it on every pass, so the range's 254 items let the add run
//! 255 times; `c + 1` must then panic exactly as vanilla Rust does.
//!
//! BEFORE (`scratchpad/stage1-w12`, this file's flags, measured 2026-10-04): the
//! build exited 0 with one warning (on `main`); both adds of `it_mid_wrap` were kernel-certified
//! under the false fact `c <= 254` (`K=254`, the range's length), their checks were
//! elided, and the program printed `0` and exited 0. The `it_mid_wrap` warning below
//! was missing and the error pattern never appeared.
//!
//! AFTER (predicted, not built): a non-header driver with a self-add before it gets
//! no trip count, `c + 1` is a refuted overflow (a warning under advisory), and the
//! program panics with `attempt to add with overflow`. Derived on the same stage 1
//! from a line-for-line twin whose range end is `std::hint::black_box(254u32)` (the
//! lane then declines, as the fix makes it): it built with exactly the two warnings
//! annotated here, and its binary panicked with that message, exit 101.

fn it_mid_wrap() -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete
    let mut c: u8 = 0;
    let mut it = 0..254u32;
    loop {
        c += 1;
        if it.next().is_none() {
            break;
        }
    }
    c + 1
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    println!("{}", it_mid_wrap());
}
