//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Coverflow-checks=on
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//! A loop counter whose constant init sits INSIDE the loop is reset every
//! iteration, so its exit test bounds nothing (TRIP-INIT-CYCLE-1).
//!
//! `loop_bounds::manual_counter_trip_count` reads `K = ceil((N - init) / stride)`
//! off a counter whose only two definitions are a constant and one checked
//! self-add. Its soundness list said that means "nothing else can reset it", but
//! `counter_init_stride_block` never asked WHERE the constant definition is. In each
//! lie function below `i = 0` runs on every iteration, so `i >= 10` never exits and
//! the loop runs until `c == limit`; `K = 10` still bounded the accumulator `c`
//! (`c <= 10`), the Clean kernel re-checked the rows under that false fact, and the
//! build removed the `c += 1` overflow check (`reset_loop(0)` returns 0 where vanilla
//! Rust panics; see `manual_counter_init_in_loop_run.rs`).
//!
//! BEFORE (`scratchpad/stage1-w12`, each revision's own flags with
//! `--emit=metadata`, measured 2026-10-04): both revisions build exit 0 with no
//! error and no warning; every row of the four lie functions is proved
//! (`TRUST_ACC_DEBUG=1`: `K=10 -> bound c <= 10`), so none of the annotations below
//! fires. `reset_idx(&[5; 11], 50)`'s `bounds` row is proved although it panics.
//!
//! AFTER (predicted, not built): a counter init on a cycle is refused, so these
//! loops get no trip count and no `c` bound. Derived on the same stage 1 from a
//! line-for-line twin in which each in-loop init reads `std::hint::black_box(0)`
//! (a call destination, which the counter recognizer already refuses): the twin
//! reports exactly the diagnostics annotated here in both revisions.
//!
//! Control: `while_ctl` (the same counter initialised ABOVE a `while i < 10`) keeps
//! `K = 10` and proves before and after, so it carries no annotation.

pub fn reset_loop(limit: u8) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
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

pub fn reset_idx(a: &[u8; 11], limit: usize) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: usize = 0;
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
    a[c]
}

pub fn let_in_loop(limit: u8) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: u8 = 0;
    loop {
        let mut i: u32 = 0;
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

pub fn retry(limit: u8) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: u8 = 0;
    loop {
        let mut tries = 0u32;
        c += 1;
        if c == limit {
            return c;
        }
        tries += 1;
        if !(tries < 10) {
            return c;
        }
    }
}

pub fn while_ctl(limit: u8) -> u8 {
    let mut c: u8 = 0;
    let mut i: u32 = 0;
    while i < 10 {
        c += 1;
        if c == limit {
            break;
        }
        i += 1;
    }
    c
}
