//@ run-pass
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ ignore-emscripten no processes
//! The run twin of `divzero_call_user_namesake.rs` (DIVZERO-NAME-1): its `usernames`
//! callers, built with verification OFF, at the counterexample the old row reported
//! (`a = 0, b = 0`, a zero step). Each returns 0 and nothing panics: the user
//! functions merely share a name with core's `div_ceil` / `rem_euclid` / `div_euclid`
//! / `Iterator::step_by` and divide by nothing, and the wrapper `util::div_ceil`
//! guards its call to core's real `div_ceil`.
//!
//! Measured 2026-10-09 on the stage 1 of `46e9afaf95` (`scratchpad/stage1-w21before`):
//! built with these flags it exits 0 and the binary exits 0. The verifying build of the
//! same callers was refused there with 14 errors (`[divzero]` / `[remzero] FAILED`).

use std::hint::black_box;

pub mod user {
    pub struct Q;
    impl Q {
        #[inline(never)]
        pub fn div_ceil(a: u32, b: u32) -> u32 {
            a ^ b
        }

        #[inline(never)]
        pub fn rem_euclid(a: u32, b: u32) -> u32 {
            a | b
        }
    }

    #[inline(never)]
    pub fn rem_euclid(a: u32, b: u32) -> u32 {
        a | b
    }

    #[inline(never)]
    pub fn div_euclid(a: u64, b: u64) -> u64 {
        a & b
    }

    pub struct S;
    impl S {
        #[inline(never)]
        pub fn step_by(&self, n: usize) -> usize {
            n
        }
    }

    pub trait Euclid {
        fn rem_euclid(&self, v: &Self) -> Self;
    }
    impl Euclid for u8 {
        #[inline(never)]
        fn rem_euclid(&self, v: &Self) -> Self {
            *self ^ *v
        }
    }

    pub fn p1(a: u32, b: u32) -> u32 {
        Q::div_ceil(a, b)
    }

    pub fn p2(a: u32, b: u32) -> u32 {
        rem_euclid(a, b)
    }

    pub fn p3(a: u64, b: u64) -> u64 {
        div_euclid(a, b)
    }

    pub fn p4(s: &S) -> usize {
        s.step_by(0)
    }

    pub fn p5(x: u8, y: u8) -> u8 {
        Euclid::rem_euclid(&x, &y)
    }

    pub fn p6(a: u32, b: u32) -> u32 {
        Q::rem_euclid(a, b)
    }
}

pub mod util {
    #[inline(never)]
    pub fn div_ceil(a: u32, b: u32) -> u32 {
        if b == 0 { 0 } else { a.div_ceil(b) }
    }

    pub fn a6(a: u32, b: u32) -> u32 {
        div_ceil(a, b)
    }
}

fn main() {
    assert_eq!(user::p1(black_box(0), black_box(0)), 0);
    assert_eq!(user::p2(black_box(0), black_box(0)), 0);
    assert_eq!(user::p3(black_box(0), black_box(0)), 0);
    assert_eq!(user::p4(black_box(&user::S)), 0);
    assert_eq!(user::p5(black_box(0), black_box(0)), 0);
    assert_eq!(user::p6(black_box(0), black_box(0)), 0);
    assert_eq!(util::a6(black_box(0), black_box(0)), 0);
    assert_eq!(util::a6(black_box(7), black_box(2)), 4);
}
