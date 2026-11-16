//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for `min_upper_bound_requires_std_min.rs`: the same user
//! `min`, built with verification ON. The overflow check in `f` must survive, so
//! `f(u32::MAX)` panics exactly as vanilla Rust does.
//!
//! BEFORE (stage 1 of `1ab78ed8e8`, `scratchpad/stage1-w10`, this file's flags,
//! measured 2026-10-03): the build exited 0 with one warning (on `main`), the
//! `+ 1` row of `f` was kernel-certified under the false `dest <= 10` fact, its check
//! was elided, and the program printed `0` and exited 0. The `f` warning below was
//! missing and the error pattern never appeared.
//!
//! AFTER (predicted; it held on the stage 1 of `936573497e`, 2026-10-04): `f`'s row is a refuted overflow (a warning under
//! advisory), nothing is elided, and the program panics with `attempt to add with
//! overflow`. Derived on the same stage 1 from two twins of this file with the user
//! callee renamed (`mn`, `max`): both built with exactly the two warnings annotated
//! here, and both binaries panicked with that message, exit 101.
//! `-Coverflow-checks=on` keeps the check whatever opt-level the suite runs at.

mod util {
    pub fn min(a: u32, _b: u32) -> u32 {
        a
    }
}

fn f(x: u32) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete
    util::min(x, 10) + 1
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    println!("{}", f(std::hint::black_box(u32::MAX)));
}
