//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on -O
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for `mid_tested_loop_counts_the_pre_test_block.rs`
//! (TRIP-MID-TEST-1), manual-counter lane: `c += 1` sits above the exit test
//! `i >= 254`, so the test continues 254 times and the add runs 255 times; `c + 1`
//! must then panic exactly as vanilla Rust does.
//!
//! BEFORE (`scratchpad/stage1-w12`, this file's flags, measured 2026-10-04): the
//! build exited 0 with one warning (on `main`); all three adds of `mid_wrap` were
//! kernel-certified under the false fact `c <= 254` (`K=254`), their checks were
//! elided, and the program printed `0` and exited 0. The `mid_wrap` warning below
//! was missing and the error pattern never appeared. `-O` is load-bearing: at
//! `-Copt-level=0` the post-loop read of `c` is not bound by the fact, and that
//! build panics today.
//!
//! AFTER (predicted, not built): `K = 255`, `c + 1` is a refuted overflow (a warning
//! under advisory), its check is kept, and the program panics with `attempt to add
//! with overflow`. Derived on the same stage 1 from a line-for-line twin with the
//! test `i >= 255` (the BEFORE lane then computes `K = 255`): it built with exactly
//! the two warnings annotated here, and its binary panicked with that message, exit
//! 101 (at the in-loop add, because the twin's loop runs once more).

fn mid_wrap() -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete
    let mut c: u8 = 0;
    let mut i: u32 = 0;
    loop {
        c += 1;
        if i >= 254 {
            break;
        }
        i += 1;
    }
    c + 1
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    println!("{}", mid_wrap());
}
