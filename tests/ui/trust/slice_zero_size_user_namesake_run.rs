//@ run-pass
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ ignore-emscripten no processes
//! The run twin of `slice_zero_size_user_namesake.rs` (SLICE-ZERO-SIZE-NAME-1): its
//! `usernames` callers, built with verification OFF, at the counterexamples the old
//! rows reported (`k = 0`, a zero size, out-of-range indices). Every call returns and
//! nothing panics: the user methods merely share a name with core's `windows` /
//! `chunks` / `rchunks_exact` / `chunks_exact` / `swap` / `split_at` and touch no slice.
//!
//! Measured 2026-10-11 on the stage 1 of `1213387e6d` (`scratchpad/stage1-w24probe`):
//! built with these flags it exits 0 and the binary exits 0, printing `7 7 0 0 7 9 0`;
//! stock `rustc` 1.97.1 prints the same. The verifying build of the same callers was
//! refused there with 17 errors (`[divzero]` / `[slice] FAILED`).

use std::hint::black_box;

pub mod user {
    pub struct Grid {
        pub w: usize,
    }

    impl Grid {
        #[inline(never)]
        pub fn windows(&self, n: usize) -> usize {
            self.w ^ n
        }

        #[inline(never)]
        pub fn chunks(&self, n: usize) -> usize {
            self.w.wrapping_add(n)
        }

        #[inline(never)]
        pub fn rchunks_exact(&self, n: usize) -> usize {
            n
        }
    }

    pub trait Tiles {
        fn chunks_exact(&self, n: usize) -> usize;
    }

    pub struct G2;

    impl Tiles for G2 {
        #[inline(never)]
        fn chunks_exact(&self, n: usize) -> usize {
            n
        }
    }

    pub trait Tr {
        fn swap(&self, i: usize, j: usize) -> usize;
        fn split_at(&self, m: usize) -> usize;
        fn windows(&self, n: usize) -> usize;
    }

    impl Tr for [u8] {
        #[inline(never)]
        fn swap(&self, i: usize, j: usize) -> usize {
            i ^ j
        }

        #[inline(never)]
        fn split_at(&self, m: usize) -> usize {
            m
        }

        #[inline(never)]
        fn windows(&self, n: usize) -> usize {
            n
        }
    }

    pub fn p1(g: &Grid, k: usize) -> usize {
        g.windows(k)
    }

    pub fn p2(g: &Grid) -> usize {
        g.chunks(0)
    }

    pub fn p3(g: &Grid) -> usize {
        g.rchunks_exact(0)
    }

    pub fn p4(g: &G2, k: usize) -> usize {
        g.chunks_exact(k)
    }

    pub fn p5(s: &[u8], i: usize, j: usize) -> usize {
        s.swap(i, j)
    }

    pub fn p6(s: &[u8], m: usize) -> usize {
        Tr::split_at(s, m)
    }

    pub fn p7(s: &[u8], n: usize) -> usize {
        Tr::windows(s, n)
    }
}

fn main() {
    let g = user::Grid { w: 7 };
    let s: &[u8] = &[1, 2, 3];
    let out = [
        user::p1(black_box(&g), black_box(0)),
        user::p2(black_box(&g)),
        user::p3(black_box(&g)),
        user::p4(black_box(&user::G2), black_box(0)),
        user::p5(black_box(s), black_box(5), black_box(2)),
        user::p6(black_box(s), black_box(9)),
        user::p7(black_box(s), black_box(0)),
    ];
    println!("{} {} {} {} {} {} {}", out[0], out[1], out[2], out[3], out[4], out[5], out[6]);
    assert_eq!(out, [7, 7, 0, 0, 7, 9, 0]);
}
