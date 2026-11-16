//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for `manual_counter_init_in_loop.rs` (TRIP-INIT-CYCLE-1):
//! `i = 0` runs on every iteration, so `i >= 10` never exits and `c += 1` runs
//! until `c == limit`. With `limit == 0` the 256th add must panic exactly as vanilla
//! Rust does.
//!
//! BEFORE (`scratchpad/stage1-w12`, this file's flags, measured 2026-10-04): the
//! build exited 0 with one warning (on `main`); both adds of `reset_loop` were kernel-certified
//! under the false fact `c <= 10` (`K=10`), their checks were elided, and the program
//! printed `0` (the 256th add wrapped `c` to 0, which equals `limit`) and exited 0.
//! The `reset_loop` warning below was missing and the error pattern never appeared.
//!
//! AFTER (predicted, not built): the in-loop init is refused, `reset_loop` gets no
//! trip count, its `c += 1` is a refuted overflow (a warning under advisory), nothing
//! is elided, and the program panics with `attempt to add with overflow`. Derived
//! on the same stage 1 from a line-for-line twin whose in-loop init reads
//! `std::hint::black_box(0)`: it built with exactly the two warnings annotated here, and
//! its binary panicked with that message, exit 101.

fn reset_loop(limit: u8) -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete
    let mut c: u8 = 0;
    let mut i: u32;
    loop {
        i = 0;
        c += 1;
        if c == limit {
            break;
        }
        i += 1;
        if i >= 10 {
            break;
        }
    }
    c
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    println!("{}", reset_loop(std::hint::black_box(0)));
}
