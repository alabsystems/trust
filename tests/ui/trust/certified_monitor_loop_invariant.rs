//@ needs-trust-verify
//@ revisions: pass entry_mismatch backedge_mismatch
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@[pass] run-pass
//@[entry_mismatch] run-crash
//@[entry_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[backedge_mismatch] run-crash
//@[backedge_mismatch] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
//! A certified E4 invariant is checked on every incoming edge to the exact
//! natural-loop header: once before the first body iteration and once after
//! each taken backedge. The two crash revisions isolate those placements so a
//! header-only or backedge-only implementation cannot pass vacuously.

#[cfg(pass)]
fn monitored_countdown(limit: u8) -> u8 {
    let mut n = limit;
    while n > 0 invariant n <= limit {
        n -= 1;
    }
    n
}

#[cfg(entry_mismatch)]
fn monitored_countdown(mut n: u8) -> u8 {
    while n > 0 invariant n == 0 {
        n -= 1;
    }
    n
}

#[cfg(backedge_mismatch)]
fn monitored_countdown(mut n: u8) -> u8 {
    while n > 0 invariant n == 2 {
        n -= 1;
    }
    n
}

#[test]
fn certified_loop_invariant_checks_entry_and_backedges() {
    assert_eq!(monitored_countdown(2), 0);
}
