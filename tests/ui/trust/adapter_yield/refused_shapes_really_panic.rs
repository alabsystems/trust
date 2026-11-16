//@ revisions: dc reuse mutref fnptr useriter overridden rtsize endwrite reassign
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: index out of bounds
//@ ignore-emscripten no processes
//! D2 tier 1 (2026-09-24): the WITNESS for the refused shapes in
//! `refused_occurrence.rs`, `refused_receiver.rs` and `item_reassigned.rs` that
//! are real bugs. Built with verification OFF, each one panics with an index out
//! of bounds — so a verifier that ever admitted `ADAPTER_YIELD` for one of them
//! would be reporting a panicking program panic-free. (The conservative
//! non-admissions — a returned `Filter`, a nested closure, `by_ref`, `..=`, a
//! generic or `async` parent — are safe programs and have no twin here.)
//!
//! Measured on the stage-1 snapshot 4e9fe36bf: every revision exits 101 with
//! `index out of bounds`.
#![allow(unused_assignments)] // `item_reassigned` overwrites its parameter on purpose

pub fn direct_call(v: &[u32]) -> bool {
    let c = |w: &[u32]| w[0] <= w[1];
    c(&[]) || v.windows(2).all(c)
}

pub fn reused(v: &[u32], u: &[u32]) -> bool {
    let c = |w: &[u32]| w[0] <= w[1];
    v.windows(2).all(c) && u.chunks(1).all(c)
}

pub fn by_mut_ref(v: &[u32]) -> bool {
    let mut c = |w: &[u32]| w[0] <= w[1];
    let r = v.windows(2).all(&mut c);
    r && c(&[])
}

pub fn fn_pointer(v: &[u32]) -> bool {
    let c = |w: &[u32]| w[0] <= w[1];
    let p: fn(&[u32]) -> bool = c;
    p(&[]) || v.windows(2).all(c)
}

pub struct Empty;
impl Iterator for Empty {
    type Item = &'static [u32];
    fn next(&mut self) -> Option<&'static [u32]> {
        Some(&[])
    }
}

pub fn user_iterator() -> bool {
    Empty.all(|w| w[0] <= w[1])
}

pub struct W<'a>(core::slice::Windows<'a, u32>);
impl<'a> Iterator for W<'a> {
    type Item = &'a [u32];
    fn next(&mut self) -> Option<&'a [u32]> {
        self.0.next()
    }
    fn all<F: FnMut(Self::Item) -> bool>(&mut self, mut f: F) -> bool {
        f(&[])
    }
}

pub fn user_override(v: &[u32]) -> bool {
    W(v.windows(2)).all(|w| w[0] <= w[1])
}

pub fn runtime_size(v: &[u32], k: usize) -> bool {
    v.windows(k).all(|w| w[0] <= w[1])
}

pub fn range_end_written(a: &[u8; 8]) -> bool {
    let mut r = 0..8;
    r.end = 9;
    r.all(|i| a[i] == 0)
}

pub fn item_reassigned(v: &[u32]) -> bool {
    v.windows(2).all(|mut w| {
        w = &[];
        w[1] == 0
    })
}

fn main() {
    let v = [1u32, 2, 3];
    let u = [1u32, 2, 3];
    let a = [0u8; 8];
    let _ = (&v, &u, &a);
    #[cfg(dc)]
    direct_call(&v);
    #[cfg(reuse)]
    reused(&v, &u);
    #[cfg(mutref)]
    by_mut_ref(&v);
    #[cfg(fnptr)]
    fn_pointer(&v);
    #[cfg(useriter)]
    user_iterator();
    #[cfg(overridden)]
    user_override(&v);
    #[cfg(rtsize)]
    runtime_size(&v, 1);
    #[cfg(endwrite)]
    range_end_written(&a);
    #[cfg(reassign)]
    item_reassigned(&v);
}
