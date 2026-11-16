//@ needs-trust-verify
//@ edition: 2021
//@ revisions: clamped clamped_len wide_arm len_arm reassigned
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[clamped] check-pass
//@[clamped_len] check-pass
//@[wide_arm] check-fail
//@[len_arm] check-fail
//@[reassigned] check-fail
//! Sweep p50 (2026-10-10): `for i in 0..k` whose end `k` is joined from two arms
//! (`let k = if n > 26 { 26 } else { n }`) bounds the payload by the value `k` held
//! when the range was built (`iterator_yield::resolve_range_bound_formula` resolves
//! the single-valued copy `_7 = copy _2` to its own name). Negative controls: an arm
//! that can exceed the bound (`wide_arm`, `len_arm`), and a conditional reassignment
//! before the range (`reassigned`), each panic for some input and stay refused.

#[cfg(clamped)]
pub fn alphabet(n: u8) -> String {
    let mut out = String::new();
    let k = if n > 26 { 26 } else { n };
    for i in 0..k {
        out.push((b'a' + i) as char);
    }
    out
}

#[cfg(clamped_len)]
pub fn prefix_sum(v: &[u32], n: usize) -> u32 {
    let k = if n > v.len() { v.len() } else { n };
    let mut s = 0u32;
    for i in 0..k {
        s = s.wrapping_add(v[i]);
    }
    s
}

#[cfg(wide_arm)]
pub fn letters(n: u8, c: bool) -> u8 {
    let k = if c { 200 } else { n.min(26) };
    let mut s = 0u8;
    for i in 0..k {
        s = s.wrapping_add(b'a' + i);
    }
    s
}

#[cfg(len_arm)]
pub fn prefix_sum_wrong(v: &[u32], n: usize) -> u32 {
    let k = if n > 100 { v.len() } else { n };
    let mut s = 0u32;
    for i in 0..k {
        s = s.wrapping_add(v[i]);
    }
    s
}

#[cfg(reassigned)]
pub fn sum4(a: &[u32; 4], n: usize, c: bool) -> u32 {
    let mut k = n.min(4);
    if c {
        k = n;
    }
    let mut s = 0u32;
    for i in 0..k {
        s = s.wrapping_add(a[i]);
    }
    s
}
