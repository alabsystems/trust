//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Cpanic=abort --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//! CALL-HAVOC-ESCAPE-1 controls (TINV-18 correction, 2026-10-06, coarse rule): the
//! dest-only call havoc keeps the facts of the two roots no callee can reach without an
//! argument — a protected, pointer-free, `Unpin` `&mut` PARAMETER that never leaves the
//! body (a scalar and a scalar struct), and a stack local that is never borrowed and
//! holds no pointer. Every add is guarded, so every one must still prove under certify.
//! (A stack local whose `&mut` never reached a call is havocked under the coarse rule:
//! `borrowed_local_is_havocked.rs` pins that precision cost.)

#[inline(never)]
fn read_only(b: &[u8]) -> usize {
    b.len()
}

pub fn mut_param(r: &mut u8, buf: &[u8]) -> u8 {
    if *r < 50 {
        let _n = read_only(buf);
        return *r + 200;
    }
    0
}

pub struct S {
    v: u8,
    w: u32,
}

pub fn mut_struct_param(s: &mut S, buf: &[u8]) -> u8 {
    if s.v < 50 {
        s.w = 1;
        let _n = read_only(buf);
        return s.v + 200;
    }
    0
}

pub fn unborrowed_local(buf: &[u8], k: u8) -> u8 {
    let mut x: u8 = 3;
    if k < 4 {
        x = k;
    }
    if x < 50 {
        let _n = read_only(buf);
        return x + 200;
    }
    0
}
