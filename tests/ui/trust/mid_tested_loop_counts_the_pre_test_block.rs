//@ revisions: default certify opt
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Coverflow-checks=on
//@[certify] compile-flags: -Ztrust-policy=certify
//@[opt] compile-flags: -O
//@ check-fail
//@ dont-check-compiler-stderr
//! Code ABOVE a loop's exit test runs once more than the test continues, and a
//! cycle that BYPASSES the test is not bounded by it at all (TRIP-MID-TEST-1).
//!
//! `loop_bounds::manual_counter_trip_count` returns `K = ceil((N - init) / stride)`,
//! the number of times the test lets the loop continue when the counter's increment
//! lands after the test. A block that runs BEFORE the test in each iteration runs
//! `K + 1` times: in `loop { c += 1; if i >= 255 { break; } i += 1; }` the test
//! continues 255 times and `c += 1` runs 256 times, yet the fact was `c <= 255`.
//! The iterator lane (`total_loop_iterations`) had the same hole for a `next()`
//! driver that is not its loop's header (`loop { c += 1; if it.next().is_none() {
//! break; } }`). And the manual lane never checked that every cycle passes through
//! the test: a `continue` above it (`skip_idx`, `skip_wrap`) loops without ever
//! testing or advancing `i`, while `K = 10` still bounded `c`.
//!
//! BEFORE (`scratchpad/stage1-w12`, each revision's own flags with
//! `--emit=metadata`, measured 2026-10-04): all three revisions build exit 0 with no
//! error and no warning. Every row of the lie functions is proved (`TRUST_ACC_DEBUG=1`:
//! `mid_idx` `K=255 -> bound c <= 255`, the real `c` is 256; `it_mid_idx` and
//! `it_mid_wrap` `K=254`, the real `c` is 255; `skip_idx` and `skip_wrap` `K=10`, `c`
//! unbounded); the `bounds` rows are kernel-certified under certify, and the overflow
//! checks of `it_mid_wrap` and `skip_wrap` are elided (`TRUST_ELIDE_DEBUG=1`), so
//! those two return wrong values (see the `_run` twins).
//!
//! AFTER (predicted, not built): the manual lane returns `K + 1` when a self-add
//! precedes the test and the counter's write does not (`mid_*`: `K = 256`), refuses
//! a test some cycle avoids (`skip_*`), and the iterator lane refuses a non-header
//! driver with a self-add before it (`it_mid_*`). Derived on the same stage 1 from a
//! line-for-line twin in which `i >= 255` reads `i >= 256` (so the BEFORE lane
//! computes the `K = 256` the fix returns), each `0..254u32` reads
//! `0..std::hint::black_box(254u32)` and each `skip_*` counter init reads
//! `std::hint::black_box(0)` (both lanes then decline, as the fix makes them): the
//! twin reports exactly the diagnostics annotated here in every revision.
//!
//! Controls, proved before and after and so unannotated: `top_idx` (the top-tested
//! `while i < 255`, `K = 255`, `c == 255` on a `[u8; 256]`), `it_top_idx` (a
//! `while let` whose driver heads its loop) and, under `-O`, `c5_like` (the
//! bottom-tested `loop { r += 1; if r > 5 { break; } }`: the counter's own add precedes
//! the test, so `K = 6` is exact and `r + 249` fits). `mid_wrap` and `c5_like` are
//! `cfg(opt)`: at `-Copt-level=0` the verifier's MIR shape leaves `mid_wrap`'s
//! post-loop read unbound and `c5_like` without a trip count, both a FAILED row
//! before and after.

pub fn mid_idx(a: &[u8; 256]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    let mut i: u32 = 0;
    loop {
        c += 1;
        if i >= 255 {
            break;
        }
        i += 1;
    }
    a[c]
}

pub fn mid_idx2(a: &[u8; 511]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    let mut i: u32 = 0;
    loop {
        c += 2;
        if i >= 255 {
            break;
        }
        i += 1;
    }
    a[c]
}

pub fn mid_idx_inloop(a: &[u8; 256]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    let mut i: u32 = 0;
    let mut s: u8 = 0;
    loop {
        c += 1;
        s = a[c];
        if i >= 255 {
            break;
        }
        i += 1;
    }
    s
}

pub fn it_mid_idx(a: &[u8; 255]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    let mut it = 0..254u32;
    loop {
        c += 1;
        let Some(_) = it.next() else { break };
    }
    a[c]
}

pub fn it_mid_wrap() -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
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

pub fn skip_idx(a: &[u8; 11], limit: usize, flag: bool) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
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
    a[c]
}

pub fn skip_wrap(limit: u8, flag: bool) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
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

#[cfg(opt)]
pub fn mid_wrap() -> u8 {
    //[opt]~^ ERROR Trust Level 0 safety verification incomplete
    //[opt]~^^ ERROR Trust strict verification failed
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

pub fn top_idx(a: &[u8; 256]) -> u8 {
    let mut c: usize = 0;
    let mut i: u32 = 0;
    while i < 255 {
        c += 1;
        i += 1;
    }
    a[c]
}

pub fn it_top_idx(a: &[u8; 255]) -> u8 {
    let mut c: usize = 0;
    let mut it = 0..254u32;
    while let Some(_) = it.next() {
        c += 1;
    }
    a[c]
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14): `c5_like` is refused under `opt` too. Since
// a39074ae82f (determinism T6, 2026-10-09) a proof session builds the MIR it verifies with
// the -O0 pipeline whatever `-O` the caller passes, so `opt` now sees the -O0 shape the
// header above describes ("`c5_like` without a trip count, ... a FAILED row"). Fail-closed:
// the `r + 249` row is FAILED, not proved.
#[cfg(opt)]
pub fn c5_like() -> u8 {
    //[opt]~^ ERROR Trust Level 0 safety verification incomplete for `mid_tested_loop_counts_the_pre_test_block::c5_like`
    //[opt]~| ERROR Trust strict verification failed for `mid_tested_loop_counts_the_pre_test_block::c5_like`
    let mut r: u8 = 0;
    loop {
        r += 1;
        if r > 5 {
            break;
        }
    }
    r + 249
}
