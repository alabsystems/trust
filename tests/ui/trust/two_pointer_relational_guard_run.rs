//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ revisions: ge_twice stale ge_twice_off stale_off
//@[ge_twice] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@[stale] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@[ge_twice_off] compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@[stale_off] compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ error-pattern: attempt to subtract with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The runtime WITNESS for `two_pointer_relational_guard.rs`'s two lies whose false
//! proof REMOVED a check: DOWNWARD-GUARD-SECOND-DEC-1 (`ge_twice`) and
//! DOWNWARD-GUARD-STALE-1 (`stale`). Each underflows `i - 1` at `a.len() == 2`.
//!
//! * `ge_twice_off`, `stale_off` — the oracle (verification off, checks on): the
//!   program panics "attempt to subtract with overflow", as vanilla Rust does.
//! * `ge_twice`, `stale` — built WITH verification (advisory, so the refutation the
//!   fix restores is a warning and the binary still builds).
//!
//! BEFORE (`scratchpad/stage1-w21before`, the stage 1 of 46e9afaf95, each revision's
//! flags, measured 2026-10-06, again 2026-10-09): the `_off` revisions panic
//! "attempt to subtract with overflow" (pass). The verified revisions build exit 0 with every row of the lie
//! function proved (`4 proved, 0 failed`); the `i - 1` overflow row was elided, the
//! subtraction WRAPPED, and the program died one step later on the bounds check
//! instead: "index out of bounds: the len is 2 but the index is
//! 18446744073709551615". The error pattern never appeared, and the WARN annotations
//! below were missing.
//!
//! AFTER (predicted, not built): the second decrement / the stale switch certify no
//! lower bound (`crates/trust-vcgen/src/generate/downward_guard_tests.rs`
//! `second_decrement_inherits_no_lower_bound`, `stale_guard_boolean_certifies_nothing`),
//! the `i - 1` row is refuted (a warning under advisory), its check is kept, and every
//! revision panics "attempt to subtract with overflow".

#[cfg(any(ge_twice, ge_twice_off))]
fn ge_twice(a: &mut [u8]) {
    //[ge_twice]~^ WARN Trust Level 0 safety verification incomplete
    let mut i = a.len();
    while i > 1 {
        i -= 1;
        i -= 1;
        a[i - 1] = 0;
    }
}

#[cfg(any(stale, stale_off))]
fn stale(a: &mut [u8]) {
    //[stale]~^ WARN Trust Level 0 safety verification incomplete
    let mut i = a.len();
    if i != 0 {
        let c = i > 1;
        i -= 1;
        if c {
            i -= 1;
            a[i - 1] = 0;
        }
    }
}

fn main() {
    let mut v = vec![0u8; 2];
    #[cfg(any(ge_twice, ge_twice_off))]
    ge_twice(std::hint::black_box(&mut v));
    #[cfg(any(stale, stale_off))]
    stale(std::hint::black_box(&mut v));
    println!("NO PANIC v={v:?}");
}
