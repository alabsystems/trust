//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on -O
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for `loop_test_block_add_runs_on_the_exit_pass.rs` (the
//! TRIP-MID-TEST-1 residual), manual-counter lane, on the proof session's own
//! pipeline: the copy-propagated `c = add_with_overflow(c, 1).0` is a non-trapping
//! checked add IN the loop's test block, so it runs on the exiting pass too: the test
//! continues 254 times, the add runs 255 times, and `c + 1` must panic exactly as
//! vanilla Rust does.
//!
//! BEFORE (the stage 1 of `76a6ea45b2`, `scratchpad/stage1-w14`, measured 2026-10-05
//! on the inliner-made `overflowing_add` twin of this shape, under
//! `-Zmir-opt-level=2`, which T6 now refuses): the fact was `c <= 254` (`K=254`), both
//! overflow checks were elided (`TRUST_ELIDE_DEBUG=1`: `elided 2`), and the program
//! printed `0` and exited 0. Built `-Ztrust-verify=off` it panicked `attempt to add
//! with overflow`, exit 101. The intrinsic shape here is the one a proof session
//! produces (`CopyProp` runs at `mir-opt-level` 1); the iterator-lane witnesses
//! below are measured the same way.
//!
//! AFTER (the stage 1 built from `40d62538d9`, measured 2026-10-05): the test
//! block's add counts as pre-test, `K = 255`, `c + 1` is a refuted overflow (a warning
//! under advisory), its check is kept, and the program panics. To be re-measured on
//! the T6 pipeline by the stage-1 UI run that lands T6.
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::add_with_overflow;

fn intr_wrap() -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete
    let mut c: u8 = 0;
    let mut i: u32 = 0;
    loop {
        c = add_with_overflow(c, 1).0;
        if i >= 254 {
            break;
        }
        i += 1;
    }
    c + 1
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    println!("{}", intr_wrap());
}
