//@ revisions: one_variant uninhabited_second wrapped option_generic const_array controls
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[one_variant] check-fail
//@[uninhabited_second] check-fail
//@[wrapped] check-fail
//@[option_generic] check-fail
//@[const_array] check-fail
//@[controls] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! ZST-ENUM-SLICE-LEN-1 (2026-10-11): a slice of a ZERO-SIZED enum must not take
//! the `len <= isize::MAX` ceiling.
//!
//! `size_of::<T>() * len <= isize::MAX` bounds a slice's length only when
//! `size_of::<T>() >= 1`; a slice of a zero-sized type can be `usize::MAX` long.
//! trust-vcgen grants the ceiling through `type_ranges::ty_is_definitely_non_zst`,
//! and that predicate read every enum through the extractor's flattened field
//! view, whose first field is a synthetic `__tag: isize`. So every enum counted as
//! sized, including `enum One { A }`, `enum Two { A, B(Infallible) }`, a generic
//! `Option<T>`, and a struct or array holding one. All of these are ZSTs.
//! `a.len() * 2` was then PROVED, KERNEL-CERTIFIED, and its overflow check ELIDED,
//! so a consumer received `0` for a `2^63`-long slice where the unverified build
//! panics (`zst_enum_slice_len_run.rs`).
//!
//! The predicate is now the alloc lane's `ty_is_definitely_nonzero_sized`, which
//! counts an enum's inhabited variants instead of its fields. The trust-ir
//! bridge's port (`native_ty_is_definitely_non_zst`) moved with it.
//!
//! BEFORE (the stage 1 of `origin/main` `2bf0ad72e3`, a copy at
//! `scratchpad/stage1-w22probe`; each revision's own flags plus
//! `--cfg <revision> --emit=metadata`, measured 2026-10-11): every revision exits
//! 0, and each bad revision reports `1 proved`, `of which 1 kernel-certified by the
//! clean CIC kernel`.
//!
//! AFTER (measured 2026-10-11, stage 1 of `618d7bd287`): each bad revision reports its row
//! FAILED (counterexample `_2 = 9223372036854775808`, 2^63) and exits 1. `controls` still proves
//! both rows: a two-variant fieldless enum is one byte (two inhabited variants
//! need a tag), and `u8` is one byte.
//!
//! COST, accepted fail-closed: a single-variant `#[repr(u8)] enum Rep { A }` IS
//! one byte, but the verifier lane stamps no enum layout, so `&[Rep]` loses its
//! ceiling too. That shape is not pinned here; `docs/DECISION_QUEUE.md`
//! ZST-ENUM-SLICE-LEN-1 records it.
#![allow(dead_code)]

use std::convert::Infallible;

#[derive(Clone, Copy)]
pub enum One {
    A,
}

#[derive(Clone, Copy)]
pub enum Two {
    A,
    B(Infallible),
}

#[derive(Clone, Copy)]
pub struct Wrap {
    pub x: One,
}

#[derive(Clone, Copy)]
pub enum Real {
    A,
    B,
}

#[cfg(one_variant)]
pub fn twice_len(a: &[One]) -> usize {
    //[one_variant]~^ ERROR Trust Level 0 safety verification incomplete
    //[one_variant]~| ERROR Trust strict verification failed
    //[one_variant]~| NOTE [overflow:mul] FAILED
    a.len() * 2
}

#[cfg(uninhabited_second)]
pub fn twice_len(a: &[Two]) -> usize {
    //[uninhabited_second]~^ ERROR Trust Level 0 safety verification incomplete
    //[uninhabited_second]~| ERROR Trust strict verification failed
    //[uninhabited_second]~| NOTE [overflow:mul] FAILED
    a.len() * 2
}

#[cfg(wrapped)]
pub fn twice_len(a: &[Wrap]) -> usize {
    //[wrapped]~^ ERROR Trust Level 0 safety verification incomplete
    //[wrapped]~| ERROR Trust strict verification failed
    //[wrapped]~| NOTE [overflow:mul] FAILED
    a.len() * 2
}

// `T = Infallible` makes `Option<T>` a ZST.
#[cfg(option_generic)]
pub fn len_plus_one<T>(a: &[Option<T>]) -> usize {
    //[option_generic]~^ ERROR Trust Level 0 safety verification incomplete
    //[option_generic]~| ERROR Trust strict verification failed
    //[option_generic]~| NOTE [overflow:add] FAILED
    a.len() + 1
}

// The unsize temp's `__slice_len == N` took the false ceiling and capped `N`.
#[cfg(const_array)]
pub fn twice_n<const N: usize>() -> usize {
    //[const_array]~^ ERROR Trust Level 0 safety verification incomplete
    //[const_array]~| ERROR Trust strict verification failed
    //[const_array]~| NOTE [overflow:mul] FAILED
    let a = [One::A; N];
    a.len() * 2
}

// The sized controls keep their ceiling: proved before and after.
#[cfg(controls)]
pub fn twice_len_real(a: &[Real]) -> usize {
    a.len() * 2
}

#[cfg(controls)]
pub fn twice_len_u8(a: &[u8]) -> usize {
    a.len() * 2
}
