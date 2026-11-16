//@ revisions: plain opt optcertify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Coverflow-checks=on
//@[opt] compile-flags: -O
//@[optcertify] compile-flags: -O -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//! The residual of TRIP-MID-TEST-1: an add in the loop TEST'S OWN BLOCK, or in a
//! `next()` driver's own two blocks, runs on the exiting pass too.
//!
//! The wave-14 fix counted a checked add that runs before a loop's exit test once
//! more than the test continues, but it looked for that add only in the blocks
//! reachable from the entry WITHOUT entering the test block
//! (`reachable_from_entry_avoiding`, which never holds the block it avoids). The test
//! block's own statements run before its `SwitchInt` on every pass, the exiting one
//! included. A trapping `c += 1` cannot sit there (its `Assert` ends the block), but a
//! NON-trapping `CheckedBinaryOp(Add, c, 1)` can: the `add_with_overflow` intrinsic
//! once `CopyProp` (which runs at `mir-opt-level` 1 and above, so in every proof
//! session) propagates its operand (`intr_mid_idx`). The iterator lane had the same
//! gap for a `next()` driver: the call block's statements and the block the call
//! returns to (above the switch on the result) run once per call, `None` included,
//! and a driver that heads its loop was exempt outright (`it_call_block_idx`,
//! `it_switch_block_idx`). A proof session never runs the MIR inliner, so
//! `Range::next` stays a call and these are the shapes every verifying session sees.
//!
//! Each lie row reads `c == 256` and indexes `[u8; 256]`: it is out of bounds in
//! every pipeline, so no revision may prove it.
//!
//! BEFORE (the stage 1 of `76a6ea45b2`, `scratchpad/stage1-w14`, measured 2026-10-05
//! under `-Zmir-opt-level=2 -Zinline-mir=no`, the explicit options T6 now refuses):
//! `intr_mid_idx`, `it_call_block_idx` and `it_switch_block_idx` each read `K=255 ->
//! bound c <= 255` and proved `a[c]` on `[u8; 256]` with `c == 256`; this file exited
//! 0 with no diagnostic. A fourth shape, `c = c.overflowing_add(1).0` in the test
//! block, needed the MIR inliner to become a non-trapping add (`overflowing_add`
//! stays a call without it, and was already refused as one), so it is not pinned
//! here: no proof session can produce it.
//!
//! AFTER (the stage 1 built from `40d62538d9`, measured 2026-10-05): the manual lane
//! counts a checked add in the test block as pre-test (`intr_mid_idx` `K=256`), and
//! the iterator lane refuses a driver whose call block or return block holds a
//! checked add (no trip count); every lie row fails. The controls (`intr_top_idx` and
//! `it_top_idx` `K=255`: the add in the loop body, after the test) proved.
//!
//! ON THE T6 PIPELINE (the stage 1 of batch 2 merged with origin/main `cc2841d66a3`,
//! measured 2026-10-09 with `TRUST_ACC_DEBUG=1` under each revision's flags): the
//! accumulator lane never takes `c` as an accumulator. At `mir-opt-level` 1 the
//! intrinsic reads `c` through a copy and reaches it back through its tuple temp and a
//! second copy (`intr_top_idx`: `_8 = copy _2; _7 = AddWithOverflow(move _8, 1);
//! _6 = copy (_7.0); _2 = move _6`), so the only
//! accumulator read is the counter `i` (`intr_mid_idx` `K=256 -> bound i <= 256`,
//! `intr_top_idx` `K=255 -> bound i <= 255`) and `a[c]` is refuted at `c == 256` in
//! EVERY row, the controls included: a false refutation of the controls, never a false
//! proof. So on this pipeline the lie rows' failure no longer tells the TRIP-MID-TEST-1
//! fix from a lane that bounds nothing; the fix stays pinned on the level-2 MIR it was
//! written for by trust-vcgen's real-MIR rows
//! (`realmir_a_test_block_add_counts_as_pre_test`,
//! `realmir_an_add_in_a_drivers_own_blocks_is_refused`). The controls carry the errors
//! they now report; a lane that bounds `c` here again turns them red, which is when this
//! file is re-measured.
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::add_with_overflow;

pub fn intr_mid_idx(a: &[u8; 256]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    let mut i: u32 = 0;
    loop {
        c = add_with_overflow(c, 1).0;
        if i >= 255 {
            break;
        }
        i += 1;
    }
    a[c]
}

pub fn it_call_block_idx(a: &[u8; 256]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    let mut it = 0..255u32;
    while let Some(_) = {
        c = add_with_overflow(c, 1).0;
        it.next()
    } {}
    a[c]
}

pub fn it_switch_block_idx(a: &[u8; 256]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    let mut it = 0..255u32;
    loop {
        let x = it.next();
        c = add_with_overflow(c, 1).0;
        let Some(_) = x else { break };
    }
    a[c]
}

pub fn intr_top_idx(a: &[u8; 256]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    let mut i: u32 = 0;
    while i < 255 {
        c = add_with_overflow(c, 1).0;
        i += 1;
    }
    a[c]
}

pub fn it_top_idx(a: &[u8; 256]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    let mut it = 0..255u32;
    while let Some(_) = it.next() {
        c = add_with_overflow(c, 1).0;
    }
    a[c]
}
