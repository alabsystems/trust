//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for `loop_driver_must_exit_on_none.rs` (TRIP-DRIVER-1):
//! `let _ = r.next();` sits on the loop's cycle but its `None` does not leave the
//! loop, so the two-item range bounds nothing and `c += 1` runs until `c == limit`.
//! With `limit == 0` the 256th add must panic exactly as vanilla Rust does.
//!
//! BEFORE (`scratchpad/stage1-w12`, this file's flags, measured 2026-10-04): the
//! build exited 0 with one warning (on `main`); the add of `stray_on_cycle` was
//! kernel-certified under the false fact `c <= 2` (`K=2`), its check was elided, and
//! the program printed `0` and exited 0. Built `-Ztrust-verify=off`, it panics
//! `attempt to add with overflow`. The `stray_on_cycle` warning below was missing and
//! the error pattern never appeared.
//!
//! AFTER (predicted, not built): the call drives no loop, `stray_on_cycle` gets no
//! trip count, its `c += 1` is a refuted overflow (a warning under advisory), and the
//! program panics with `attempt to add with overflow`. Derived on the same stage 1
//! from a line-for-line twin whose range end reads `std::hint::black_box(2u32)`: it
//! built with exactly the two warnings annotated here, and its binary panicked with
//! that message, exit 101.

fn stray_on_cycle(limit: u8) -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete
    let mut r = 0..2u32;
    let mut c: u8 = 0;
    loop {
        let _ = r.next();
        c += 1;
        if c == limit {
            break;
        }
    }
    c
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    println!("{}", stray_on_cycle(std::hint::black_box(0)));
}
