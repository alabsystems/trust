//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Coverflow-checks=on
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//! A loop that runs ZERO times does not cancel the other loops' trip counts
//! (TRIP-ZERO-PRODUCT-1).
//!
//! `loop_bounds::total_loop_iterations` bounds how many times a self-add can run by
//! the PRODUCT of every `next`-driven loop's trip count. That product is an upper
//! bound only when every factor is at least 1: a zero-trip loop anywhere in the
//! body (`0..WARMUP` with `WARMUP == 0`, `0..0`, a `for` over a `&[u8; 0]`, or an
//! empty inner loop) made it 0. `build_accumulator_bound_facts` then emitted the
//! global fact `c <= 0` although the other loop adds 300 times; the Clean kernel
//! re-checked each row below under that false hypothesis, and the build removed the
//! overflow check (`count_after_warmup` returns 44 where vanilla Rust panics; see
//! `loop_trip_zero_factor_is_not_a_bound_run.rs`).
//!
//! BEFORE (`scratchpad/stage1-w12`, each revision's own flags with
//! `--emit=metadata`, measured 2026-10-04): both revisions build exit 0 with no
//! error and no warning. Every row of the five lie functions is proved
//! (`TRUST_ACC_DEBUG=1`: `K=0 -> bound c <= 0` in each; `TRUST_ELIDE_DEBUG=1`:
//! `elided 1` in each), so none of the annotations below fires.
//!
//! AFTER (predicted, not built): each factor is `max(1, tc)`, so `K = 300` and the
//! fact is `c <= 300`. The annotations were derived on the same stage 1 from a
//! line-for-line twin of this file in which every zero-trip loop runs once instead
//! (`WARMUP = 1`, `0..1u32`, `&[u8; 1]`), which is exactly the factor the clamp
//! gives: the twin reports exactly the diagnostics annotated here in both
//! revisions (`K=300 -> bound c <= 300`; `count_after_warmup` and `zero_after`
//! `[overflow:add] FAILED`, the three `a[c]` rows `bounds FAILED`).
//!
//! Controls: `one_then` (a `0..1` loop, then 300 adds into a `[u8; 301]`) and
//! `safe_after_zero` (a zero-trip loop, then 200 adds on `u8`) prove before and
//! after, so they carry no annotation (compiletest requires every ERROR and WARN to
//! be annotated).

const WARMUP: u32 = 0;

pub fn count_after_warmup() -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: u8 = 0;
    for _ in 0..WARMUP {}
    for _ in 0..300u32 {
        c += 1;
    }
    c
}

pub fn zero_then(a: &[u8; 1]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    for _ in 0..0u32 {}
    for _ in 0..300u32 {
        c += 1;
    }
    a[c]
}

pub fn empty_arr_then(e: &[u8; 0], a: &[u8; 1]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    for _ in e {}
    for _ in 0..300u32 {
        c += 1;
    }
    a[c]
}

pub fn nested_zero(a: &[u8; 1]) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
    for _ in 0..300u32 {
        c += 1;
        for _ in 0..0u32 {}
    }
    a[c]
}

pub fn zero_after() -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: u8 = 0;
    for _ in 0..300u32 {
        c += 1;
    }
    for _ in 0..0u32 {}
    c
}

pub fn one_then(a: &[u8; 301]) -> u8 {
    let mut c: usize = 0;
    for _ in 0..1u32 {}
    for _ in 0..300u32 {
        c += 1;
    }
    a[c]
}

pub fn safe_after_zero() -> u8 {
    let mut c: u8 = 0;
    for _ in 0..0u32 {}
    for _ in 0..200u32 {
        c += 1;
    }
    c
}
