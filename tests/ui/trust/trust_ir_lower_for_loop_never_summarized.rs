//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! A `for` loop the direct producer cannot lower faithfully must FAIL `-Ztrust-ir-lower=strict`;
//! it may not pass as a lowered body with the loop summarized away.
//!
//! Until 2026-10-01 the wave-ER read-only-escape summary (f7b7cc0bd6) replaced a `for` loop with
//! an `undef` rebind of the locals it mutated whenever a structural scan saw no write to a
//! non-local place, and the body carried NO unsupported tag. Strict reads only that tag list, so
//! this file compiled under strict on main f5dd1d805a (measured: exit 0, no error) while the
//! trust-ir of its three bodies was:
//!
//!   close_range   `ret`                      — the `close` calls gone
//!   sum_range     `%s = undef u32; ret %s`   — the sum gone
//!   count_slice   `%s = undef u32; ret %s`
//!
//! The summary is removed. A `for` now takes the faithful lanes or declines with a tag, so
//! strict sees exactly what was lowered: the two integer-range loops lower as real loops (the
//! wave-FR counting protocol; `tests/run-make/trust-for-loop-no-erasure` checks the IR), and the
//! slice loop — which no lane models yet — is a strict error naming its shape. That error is the
//! point of this file: it is what "summarized" honestly costs.

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

pub fn close_range(lo: i32, hi: i32) {
    for fd in lo..hi {
        unsafe {
            close(fd);
        }
    }
}

pub fn sum_range(n: u32) -> u32 {
    let mut s = 0u32;
    for i in 0..n {
        s = s.wrapping_add(i);
    }
    s
}

pub fn count_slice(v: &[u32]) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let mut s = 0u32;
    for x in v {
        s = s.wrapping_add(*x);
    }
    s
}
