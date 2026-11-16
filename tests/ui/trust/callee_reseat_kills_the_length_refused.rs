//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! A user callee that RESEATS a slice or str through `&mut` changes its length, so a
//! bound established before the call must not reach a use after it. Each panics on
//! the input named beside it.
//!
//! MEASURED FALSE PROOFS, 2026-09-29 (an audit of `3b4293d06cb`): every function
//! below was PROVED and panicked. The callee's havoc is refined to its exact write
//! path `s*` (`callee_write_set`), whose length `s*__slice_len` only the derived
//! slice-length channel reaches, and that commit had withheld the channel from
//! every havoc name. `callee_writes_elements_keeps_the_length.rs` is the twin a
//! callee that writes ELEMENTS must keep proving.

pub fn sset<'a>(s: &mut &'a [u8], t: &'a [u8]) {
    *s = t;
}

pub fn set<'a>(s: &mut &'a str, t: &'a str) {
    *s = t;
}

// s = [1, 2, 3], t = [], i = 2.
pub fn slice_after_reseat<'a>(s: &mut &'a [u8], t: &'a [u8], i: usize) -> &'a [u8] { //~ ERROR failed for `callee_reseat_kills_the_length_refused::slice_after_reseat`
    if i <= s.len() {
        sset(s, t);
        &s[..i]
    } else {
        &[]
    }
}

// t = [1], u = []: `0 - 1`.
pub fn length_after_reseat<'a>(t: &mut &'a [u8], u: &'a [u8]) -> usize { //~ ERROR failed for `callee_reseat_kills_the_length_refused::length_after_reseat`
    if t.len() > 0 {
        sset(t, u);
        t.len() - 1
    } else {
        0
    }
}

// s = "abc", t = "", i = 1.
pub fn str_index_after_reseat<'a>(s: &mut &'a str, t: &'a str, i: usize) -> u8 { //~ ERROR failed for `callee_reseat_kills_the_length_refused::str_index_after_reseat`
    if i < s.len() {
        set(s, t);
        s.as_bytes()[i]
    } else {
        0
    }
}

pub struct P<'a> {
    pub a: &'a str,
    pub b: &'a str,
}

pub fn reset(p: &mut P<'_>) {
    p.a = p.b;
}

// p = P { a: "abc", b: "" }, i = 1.
pub fn field_after_reseat(p: &mut P<'_>, i: usize) -> u8 { //~ ERROR failed for `callee_reseat_kills_the_length_refused::field_after_reseat`
    let n = p.a.len();
    reset(p);
    if i < n { p.a.as_bytes()[i] } else { 0 }
}

pub fn swap_fields<'a>(p: &mut (&'a str, &'a str)) {
    let x = p.0;
    p.0 = p.1;
    p.1 = x;
}

// p = ("abc", ""), i = 1.
pub fn tuple_after_swap<'a>(p: &mut (&'a str, &'a str), i: usize) -> u8 { //~ ERROR failed for `callee_reseat_kills_the_length_refused::tuple_after_swap`
    if i < p.0.len() {
        swap_fields(p);
        p.0.as_bytes()[i]
    } else {
        0
    }
}

// s = [1, 2, 3], t = [], i = 2: the length read before the call, the slice through a
// copy of the reseated pointer.
pub fn copy_after_reseat<'a>(s: &mut &'a [u8], t: &'a [u8], i: usize) -> &'a [u8] { //~ ERROR failed for `callee_reseat_kills_the_length_refused::copy_after_reseat`
    let n = s.len();
    sset(s, t);
    let r: &'a [u8] = *s;
    if i <= n { &r[..i] } else { r }
}

pub struct H<'a> {
    pub d: &'a [u8],
    pub k: usize,
}

pub fn seth<'a>(h: &mut H<'a>, t: &'a [u8]) {
    h.d = t;
}

// h = H { d: [1, 2, 3], k: 0 }, t = [], i = 1: a setter method's shape.
pub fn field_slice_after_reseat<'a>(h: &mut H<'a>, t: &'a [u8], i: usize) -> u8 { //~ ERROR failed for `callee_reseat_kills_the_length_refused::field_slice_after_reseat`
    let n = h.d.len();
    std::hint::black_box(());
    seth(h, t);
    let r = h.d;
    if i < n { r[i] } else { 0 }
}
