//@ revisions: default certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! S2 (2026-10-16): a refutation that names a loop-carried JOIN symbol — the
//! value of a name at a loop header, which has a back-edge operand and no defining
//! equation — is withheld when no value the join takes in the first passes over
//! its loop satisfies the query.
//!
//! `bulk_3byte` is aterm-parser `utf8_simd.rs:61`'s shape: `i + 3` is read at the
//! header of a loop whose exit test is an opaque call, and the solver chose
//! `i = 2^64 - 3` beside an empty slice. Now `UNKNOWN` with the held reason; the
//! build is still an error.
//!
//! Negative controls: `pre`'s `x + 1` runs before the loop and never reads the
//! join; `x = 255` is a real bug and stays `FAILED` in a body that HAS joins.
//! `in_loop`'s `r += 1` reads the join of `r` and overflows on the sixth pass: a
//! shallow value satisfies the query, so the genuine in-loop bug stays `FAILED`.
//!
//! MEASURED 2026-10-20 on the stage 1 of the SRH-1 land merge: `bulk_3byte`'s
//! `[overflow:add]` row is `UNKNOWN`, withheld on the join of `i` (`i#s0_0_s8_0`
//! in `default`); `pre` and `in_loop` are `[overflow:add] FAILED` (`default`'s
//! `pre` counterexample has `x = 255`), in both revisions.

pub struct Out {
    n: usize,
}

impl Out {
    #[inline(never)]
    pub fn is_full(&self) -> bool {
        std::hint::black_box(self.n) >= 16
    }
}

pub fn bulk_3byte(bytes: &[u8], out: &Out) -> usize {
    //~^ NOTE generic solver counterexample withheld: loop-carried value at a loop header has no defining equation
    let mut i = 0usize;
    while !out.is_full() {
        match bytes.get(i..i + 3) {
            Some(_) => i += 3,
            None => break,
        }
    }
    i
}

pub fn pre(x: u8, n: u32) -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    let y = x + 1;
    let mut i = 0;
    while i < n {
        i += 1;
    }
    y
}

pub fn in_loop(n: u8) -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    let mut r: u8 = 250;
    let mut k = 0;
    while k < n {
        r += 1;
        k += 1;
    }
    r
}
