//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to subtract with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! A `&mut v` handed to a USER trait method named `deref_mut` may resize `v`, even
//! when the method's trait argument spells std's `DerefMut` (SLICE-VIEW-ANCHOR-1).
//!
//! `guards::local_mut_borrows_may_resize` counts a `&mut v` consumed by std `Vec`'s
//! own `DerefMut::deref_mut` as length-benign (the `v.sort()` idiom), which keeps the
//! `.len()` tie alive across it. `callee_is_std_vec_slice_view` recognized that call
//! by the method tail plus `contains(" as core::ops::deref::DerefMut>::deref_mut")`.
//! The call below renders
//! `<alloc::vec::Vec<u32> as …::Shrink<for<'_> fn(&'_ mut …::X) -> &'_ mut
//! <…::X as core::ops::deref::Deref>::Target
//! {<…::X as core::ops::deref::DerefMut>::deref_mut}>>::deref_mut`:
//! the needle sits inside the fn item that is `Shrink`'s generic argument, and the
//! body is this file's, which truncates `v`.
//!
//! BEFORE (the stage 1 of `fc62d8ba05`, `integ/wave12`, 2026-10-04; the wave-12 review
//! measured the same on the stage 1 of `ee3f51541d` under default, strict, certify,
//! memory-safe and advisory, and on `stage1-w11fix`): `TRUST_ELIDE_DEBUG=1` prints
//! `elided 1 kernel-certified overflow checks` in `user_len`, this file built with
//! exactly these flags exits 0, and the binary prints `18446744073709551615` and
//! exits 0. Renamed to `shrink`, the method is not counted benign and the binary
//! panics.
//!
//! AFTER: the `deref` arm of `callee_is_std_vec_slice_view` is
//! `std_container_deref_self(callee) == Some(Vec)`, the callee split at its TOP-LEVEL
//! ` as ` with the trait-and-method half EQUAL to std's, and the benign count also
//! requires the receiver's MIR type to be std's `Vec`. The `&mut v` here may resize,
//! no tie is kept, the check stays, and the run panics. The `deref` twin is
//! `slice_view_user_trait_deref_run.rs`; the trust-vcgen pin is
//! `crates/trust-vcgen/src/guards_slice_view_anchor_tests.rs`.

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

// A USER trait, generic over `F`, whose method is NAMED `deref_mut`; it empties the `Vec`.
pub trait Shrink<F> {
    fn deref_mut(&mut self, f: F);
}

impl<F> Shrink<F> for Vec<u32> {
    fn deref_mut(&mut self, _f: F) {
        self.truncate(0);
    }
}

#[inline(never)]
pub fn user_len(mut v: Vec<u32>) -> usize {
    if v.len() == 0 {
        return 0;
    }
    // `F` is the fn ITEM type `{<X as DerefMut>::deref_mut}`.
    Shrink::deref_mut(&mut v, <X as DerefMut>::deref_mut);
    v.len() - 1
}

fn main() {
    println!("{}", user_len(std::hint::black_box(vec![7])));
}
