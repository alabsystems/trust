//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for the bypass rows of
//! `mid_tested_loop_counts_the_pre_test_block.rs` (TRIP-MID-TEST-1): with `flag`
//! set, the `continue` loops back above the counter test `i >= 10` without testing
//! or advancing `i`, so `c += 1` runs until `c == limit`. With `limit == 0` the 256th
//! add must panic exactly as vanilla Rust does.
//!
//! BEFORE (`scratchpad/stage1-w12`, this file's flags, measured 2026-10-04): the
//! build exited 0 with one warning (on `main`); both adds of `skip_wrap` were
//! kernel-certified under the false fact `c <= 10` (`K=10`), their checks were
//! elided, and the program printed `0` and exited 0. The `skip_wrap` warning below
//! was missing and the error pattern never appeared.
//!
//! AFTER (predicted, not built): a counter test that some cycle avoids bounds
//! nothing, so `skip_wrap` gets no trip count, its `c += 1` is a refuted overflow (a
//! warning under advisory), and the program panics with `attempt to add with
//! overflow`. Derived on the same stage 1 from a line-for-line twin whose counter
//! init reads `std::hint::black_box(0)` (the lane then declines, as the fix makes
//! it): it built with exactly the warnings annotated here, and its binary panicked
//! with that message, exit 101.

fn skip_wrap(limit: u8, flag: bool) -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete
    let mut c: u8 = 0;
    let mut i: u32 = 0;
    loop {
        c += 1;
        if c == limit {
            break;
        }
        if flag {
            continue;
        }
        i += 1;
        if i >= 10 {
            break;
        }
    }
    std::hint::black_box(c)
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    println!("{}", skip_wrap(std::hint::black_box(0), std::hint::black_box(true)));
}
