//@ revisions: default strict certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//! The control for `owned_vec_name_requires_std_vec.rs` (OWNED-VEC-NAME-1): the same
//! code under names that are not `Vec`/`String`. A container type is recognized by
//! its exact std path after the fix and was recognized by its last path segment
//! before, so these types were never admitted. Every revision refuses all three
//! functions both before and after the fix.
//!
//! Measured on the stage 1 of `38e6c69b1c` (`scratchpad/stage1-w11fix`; each
//! revision's flags with `--emit=metadata`, 2026-10-04): every annotation below fires
//! under default, strict and certify, and nothing else is reported. `h2_wrap` and
//! `s2_wrap` read `overflow:sub` FAILED (ay-in-process). `k_wrap`'s `slice` row reads
//! unknown. With the types named `Vec` and `String`, that file's `h2`, `k` and `s2`
//! were proved, so the name alone decided the verdict. On the stage 1 of `ee3f51541d`
//! (2026-10-04) every annotation still fires; `k_wrap`'s `slice` row reads failed there,
//! since DEREF-ANCHOR-1 no longer hops this `Deref`.

use std::cell::Cell;

/// The same code as `owned_vec_name_requires_std_vec.rs`'s user `Vec`, named `Wrap`.
pub struct Wrap {
    pub a: std::vec::Vec<u32>,
    pub b: std::vec::Vec<u32>,
    pub flip: Cell<bool>,
}

impl core::ops::Deref for Wrap {
    type Target = std::vec::Vec<u32>;
    fn deref(&self) -> &std::vec::Vec<u32> {
        let f = self.flip.get();
        self.flip.set(!f);
        if f { &self.b } else { &self.a }
    }
}

pub fn h2_wrap(w: &Wrap) -> usize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `owned_vec_name_requires_std_vec_wrap_control::h2_wrap`
    //~| ERROR Trust strict verification failed for `owned_vec_name_requires_std_vec_wrap_control::h2_wrap`
    if w.is_empty() {
        return 0;
    }
    w.len() - 1
}

pub fn k_wrap(w: &Wrap, i: usize) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `owned_vec_name_requires_std_vec_wrap_control::k_wrap`
    //~| ERROR Trust strict verification failed for `owned_vec_name_requires_std_vec_wrap_control::k_wrap`
    if i < w.len() { w[i] } else { 0 }
}

/// The same code as that file's user `String`, named `SWrap`.
pub struct SWrap {
    pub a: std::string::String,
    pub b: std::string::String,
    pub flip: Cell<bool>,
}

impl core::ops::Deref for SWrap {
    type Target = std::string::String;
    fn deref(&self) -> &std::string::String {
        let f = self.flip.get();
        self.flip.set(!f);
        if f { &self.b } else { &self.a }
    }
}

pub fn s2_wrap(w: &SWrap) -> usize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `owned_vec_name_requires_std_vec_wrap_control::s2_wrap`
    //~| ERROR Trust strict verification failed for `owned_vec_name_requires_std_vec_wrap_control::s2_wrap`
    if w.is_empty() {
        return 0;
    }
    w.len() - 1
}
