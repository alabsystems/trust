//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! A callee that REASSIGNS its own `&mut` formal and then writes through it writes
//! the memory the formal now points at. Each panics on the input named beside it.
//!
//! MEASURED FALSE PROOFS, 2026-09-29 (an adversarial audit): the callee write-set
//! called the reassignment caller-invisible and kept charging later `(*p)` writes to
//! the formal's own argument, so the call-site refinement dropped the other
//! argument's havoc with nothing put back. Three were newly reachable today through
//! the `str::len` rewrite, the array-field confinement and the whole-pointee store.

pub struct P<'a> {
    pub d: &'a [u8],
    pub k: usize,
}

fn f<'a, 'b>(mut p: &'b mut P<'a>, q: &'b mut P<'a>) {
    p.k = 1;
    p = q;
    p.d = &[];
}

// a = P { d: [1], k: 0 }, b = P { d: [1, 2, 3], k: 0 }, i = 1.
pub fn emptied_through_the_other<'a>(a: &mut P<'a>, b: &mut P<'a>, i: usize) -> u8 { //~ ERROR failed for `callee_reseats_its_formal_refused::emptied_through_the_other`
    if i < b.d.len() {
        f(a, b);
        b.d[i]
    } else {
        0
    }
}

fn g<'a, 'b>(mut p: &'b mut P<'a>, q: &'b mut P<'a>) {
    p = q;
    p.k = 100;
}

// b.k = 0.
pub fn field_through_the_other<'a>(a: &mut P<'a>, b: &mut P<'a>, buf: &[u8; 4]) -> u8 { //~ ERROR failed for `callee_reseats_its_formal_refused::field_through_the_other`
    if b.k < 4 {
        g(a, b);
        buf[b.k]
    } else {
        0
    }
}

fn h<'a, 'b>(mut p: &'b mut &'a str, q: &'b mut &'a str, t: &'a str) {
    p = q;
    *p = t;
}

// b = "abc", t = "", i = 1.
pub fn str_through_the_other<'a>(a: &mut &'a str, b: &mut &'a str, t: &'a str, i: usize) -> u8 { //~ ERROR failed for `callee_reseats_its_formal_refused::str_through_the_other`
    if i < b.len() {
        h(a, b, t);
        b.as_bytes()[i]
    } else {
        0
    }
}

fn set<'b>(mut p: &'b mut usize, q: &'b mut usize) {
    p = q;
    *p = 100;
}

// any a, b.
pub fn stored_value_through_the_other(a: &mut usize, b: &mut usize, buf: &[u8; 4]) -> u8 { //~ ERROR failed for `callee_reseats_its_formal_refused::stored_value_through_the_other`
    *b = 2;
    set(a, b);
    buf[*b]
}
