//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! CALL-HAVOC-ESCAPE-1, the coarse rule's pinned precision cost (TINV-18 correction,
//! 2026-10-06): a stack local whose `&mut` is taken anywhere in the body is havocked at
//! every call, even a call whose arguments grant no write and even when the borrow never
//! reached a call. This program never overflows (`x` is 7 at the add), but the guard
//! `x < 50` does not survive `read_only(buf)`, so the row is refuted. The fine-grained
//! exposure analysis that proved it missed a pointer stored THROUGH another `&mut`
//! (`review_round_three_shapes.rs::stored_through_a_mut`); this pin flips only with a
//! reviewed refinement that recovers it soundly.

#[inline(never)]
fn read_only(b: &[u8]) -> usize {
    b.len()
}

pub fn borrowed_local(buf: &[u8]) -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    let mut x: u8 = 3;
    let r = &mut x;
    *r = 7;
    if x < 50 {
        let _n = read_only(buf);
        return x + 200;
    }
    0
}
