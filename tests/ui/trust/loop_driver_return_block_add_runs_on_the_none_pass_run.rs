//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for `loop_test_block_add_runs_on_the_exit_pass.rs` (the
//! TRIP-MID-TEST-1 residual), iterator lane: a non-trapping checked add sits in
//! the block the `next()` call returns to, above the switch on its result. That
//! block runs once per `next()` call, the `None` one included, so the range's 254
//! items let the add run 255 times, and `c + 1` must panic exactly as vanilla Rust
//! does. A proof session never runs the MIR inliner, so `Range::next` stays a call
//! and the driver is there; `CopyProp` (`mir-opt-level` 1 and above, so every proof
//! session) copy-propagates the intrinsic's operand, so the add is a self-add.
//!
//! BEFORE (the stage 1 of `76a6ea45b2`, `scratchpad/stage1-w14`, measured 2026-10-05
//! with `-Zmir-opt-level=2 -Zinline-mir=no` added — the explicit options T6 now
//! refuses; this file now runs on the proof session's own pipeline): the build
//! exited 0 with one warning (on `main`); the fact was `c <= 254` (`K=254`), the
//! overflow check of `c + 1` was elided
//! (`TRUST_ELIDE_DEBUG=1`: `elided 1`), and the program printed `0` and exited 0.
//! Built `-Ztrust-verify=off` with the same other flags it panicked `attempt to add
//! with overflow`, exit 101.
//!
//! AFTER (the stage 1 built from `40d62538d9`, measured 2026-10-05, `x.py test
//! --stage 1`, with the same added options): a driver whose own blocks hold a checked
//! add gets no trip count, `c + 1` is a refuted overflow (a warning under advisory),
//! its check is kept, and the program panics. To be re-measured on the T6 pipeline by
//! the stage-1 UI run that lands T6.
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::add_with_overflow;

fn it_return_block_wrap() -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete
    let mut c: u8 = 0;
    let mut it = 0..254u32;
    loop {
        let x = it.next();
        c = add_with_overflow(c, 1).0;
        let Some(_) = x else { break };
    }
    c + 1
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    println!("{}", it_return_block_wrap());
}
