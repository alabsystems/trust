//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Coverflow-checks=on
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//! An `Iterator::next` call on a loop's cycle bounds that loop only when the loop
//! EXITS on its `None`, CONTINUES on its `Some`, and its iterator is built OUTSIDE
//! the loop (TRIP-DRIVER-1).
//!
//! `loop_bounds::total_loop_iterations` took every `next()` call on a cycle as a loop
//! driver and checked only that there were as many of them as loops. In every lie
//! function below that count balanced while no call bounded the loop doing the adding:
//! `let _ = r.next();` inside a `loop` that exits on `c == limit` (`stray_on_cycle`),
//! a manual `while` balanced by a second `next` in ANOTHER loop (`two_next`,
//! `nested_balance`), a `None` arm that continues (`none_continues`), and an iterator
//! rebuilt on every pass, which never runs out (`fresh_each_iter`,
//! `fresh_each_iter_let`). Each read `K = 1` or `K = 2`, the `c += 1` row was
//! kernel-certified under `c <= K`, and its check was elided (`stray_on_cycle(0)`
//! returns 0 where vanilla Rust panics; see `loop_driver_must_exit_on_none_run.rs`).
//!
//! BEFORE (`scratchpad/stage1-w12`, each revision's own flags with
//! `--emit=metadata`, measured 2026-10-04): both revisions build exit 0 with no
//! error and no warning; every row of the six lie functions is proved
//! (`TRUST_ACC_DEBUG=1`: `K=2` for `stray_on_cycle`, `fresh_each_iter*` and
//! `none_continues`, `K=1` for `two_next` and `nested_balance`) and `TRUST_ELIDE_DEBUG=1`
//! reports their overflow checks elided, so none of the annotations below fires.
//!
//! AFTER (predicted, not built): no call in these functions drives the loop that adds,
//! so they get no trip count. Derived on the same stage 1 from a line-for-line twin in
//! which each range end in a lie function reads `std::hint::black_box(..)` (the BEFORE
//! lane then has no trip count either): the twin reports exactly the diagnostics
//! annotated here in both revisions.
//!
//! Controls, proved before and after and so unannotated: `plain_for` (`K = 2`),
//! `matrix` (a nested `for`, `K = 12`) and `outer_add_nested` (an add in the outer body
//! of a nested `for`, `K = 12`).

pub fn stray_on_cycle(limit: u8) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
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

pub fn two_next(limit: u8) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut r = 0..1u32;
    let mut c: u8 = 0;
    let mut j: u32 = 0;
    while j < 1000 {
        c += 1;
        j += 1;
        if c == limit {
            break;
        }
    }
    for _ in 0..1u32 {
        let _ = r.next();
    }
    c
}

pub fn nested_balance(limit: u8) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut r = 0..1u32;
    let mut c: u8 = 0;
    let mut j: u32 = 0;
    while j < 1000 {
        c += 1;
        j += 1;
        if c == limit {
            break;
        }
        for _ in 0..1u32 {
            let _ = r.next();
        }
    }
    c
}

pub fn none_continues(limit: u8) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut r = 0..2u32;
    let mut c: u8 = 0;
    loop {
        match r.next() {
            None => {}
            Some(_) => {}
        }
        c += 1;
        if c == limit {
            break;
        }
    }
    c
}

pub fn fresh_each_iter(limit: u8) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: u8 = 0;
    loop {
        let mut r = 0..2u32;
        if r.next().is_none() {
            break;
        }
        c += 1;
        if c == limit {
            break;
        }
    }
    c
}

pub fn fresh_each_iter_let(limit: u8) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~^^ ERROR Trust strict verification failed
    let mut c: u8 = 0;
    loop {
        let mut r = 0..2u32;
        let Some(_) = r.next() else { break };
        c += 1;
        if c == limit {
            break;
        }
    }
    c
}

pub fn plain_for(limit: u8) -> u8 {
    let mut c: u8 = 0;
    for _ in 0..2u32 {
        c += 1;
        if c == limit {
            break;
        }
    }
    c
}

pub fn matrix(a: &[[u8; 4]; 3]) -> u32 {
    let mut t: u32 = 0;
    for i in 0..3usize {
        for j in 0..4usize {
            t += a[i][j] as u32;
        }
    }
    t
}

pub fn outer_add_nested(a: &[[u8; 4]; 3]) -> u32 {
    let mut n: u32 = 0;
    let mut t: u32 = 0;
    for i in 0..3usize {
        n += 1;
        for j in 0..4usize {
            t += a[i][j] as u32;
        }
    }
    n + t
}
