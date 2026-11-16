//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to subtract with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! A USER trait method named `deref` on std's `Vec` is not `Vec`'s slice view, even
//! when its trait argument spells std's `DerefMut` (SLICE-VIEW-ANCHOR-1).
//!
//! `guards::slice_last_some_nonempty_definitions` ties a std `Vec` view to its `Vec`
//! (`slice_len(s) == coll_len(v)`) when `callee_is_std_vec_slice_view` accepts the
//! call. It recognized the call by the method tail plus a `contains` test for std's
//! `Deref`/`DerefMut` spelling anywhere in the callee. The call below renders
//! `<alloc::vec::Vec<u32> as …::View<for<'_> fn(&'_ mut …::X) -> … {<…::X as
//! core::ops::deref::DerefMut>::deref_mut}>>::deref`, and the body returns `&[]`.
//!
//! BEFORE (the stage 1 of `fc62d8ba05`, `integ/wave12`, 2026-10-04; the wave-12 review
//! measured the same under advisory on the stage 1 of `ee3f51541d` and on
//! `stage1-w11fix`): `TRUST_ELIDE_DEBUG=1` prints `elided 1 kernel-certified overflow
//! checks` in `view_len`, this file built with exactly these flags exits 0, and the
//! binary prints `18446744073709551615` and exits 0. Renamed to `view`, the method
//! gets no equation and the binary panics.
//!
//! AFTER: the exact top-level split refuses the call (and the view equation also
//! requires the receiver's MIR type to be std's `Vec`), so `s.len()` is unconstrained,
//! the check stays, and the run panics. The `deref_mut` twin is
//! `slice_view_user_trait_deref_mut_run.rs`.

use std::ops::{Deref, DerefMut};

pub struct X(Vec<u32>);

impl Deref for X {
    type Target = Vec<u32>;
    fn deref(&self) -> &Vec<u32> {
        &self.0
    }
}

impl DerefMut for X {
    fn deref_mut(&mut self) -> &mut Vec<u32> {
        &mut self.0
    }
}

// A USER trait whose method is NAMED `deref`; it returns an EMPTY view.
pub trait View<F> {
    fn deref(&self, f: F) -> &[u32];
}

impl<F> View<F> for Vec<u32> {
    fn deref(&self, _f: F) -> &[u32] {
        &[]
    }
}

#[inline(never)]
pub fn view_len(v: Vec<u32>) -> usize {
    if v.len() == 0 {
        return 0;
    }
    let s = View::deref(&v, <X as DerefMut>::deref_mut);
    s.len() - 1
}

fn main() {
    println!("{}", view_len(std::hint::black_box(vec![7])));
}
