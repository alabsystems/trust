//@ needs-trust-verify
//@ edition: 2021
//@ revisions: owned unguarded reseat two_boxes mut_reseat swapped
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[owned] check-pass
//@[unguarded] check-fail
//@[reseat] check-fail
//@[two_boxes] check-fail
//@[mut_reseat] check-fail
//@[swapped] check-fail
//! A guarded index into an owned `Box<[T]>` (2026-10-08; ordinary-Rust sweep
//! `c90b_boxed_slice_owned`). rustc elaborates every `*b` into a FRESH
//! `copy (b.0.0) as *const [T]` temp, so `b.len()` and `b[i]` read the lengths of
//! two different temps. Each cast now ties its temp's length (and its pointee's)
//! to the box's own fat pointer, and the cast itself, a `repr(transparent)` core
//! pointer wrapper to the raw pointer it wraps, is admitted as infallible.
//!
//! Every other revision PANICS on some input and must stay refused: no guard; the
//! box replaced by an empty one between the guard and the index (by value, and
//! through `&mut`); a guard on one box with the index into another; and (the control
//! review round 80 proposed, refused on the bounds row itself rather than on the
//! `Box::new([])` lowering) the box replaced by ANOTHER box between guard and index.

#[cfg(owned)]
pub fn f(b: Box<[u32]>, i: usize) -> u32 {
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(unguarded)]
pub fn f(b: Box<[u32]>, i: usize) -> u32 {
    b[i]
}

#[cfg(reseat)]
pub fn f(mut b: Box<[u32]>, i: usize) -> u32 {
    if i < b.len() {
        b = Box::new([]);
        b[i]
    } else {
        0
    }
}

#[cfg(two_boxes)]
pub fn f(a: Box<[u32]>, b: Box<[u32]>, i: usize) -> u32 {
    if i < a.len() { b[i] } else { 0 }
}

#[cfg(mut_reseat)]
pub fn f(b: &mut Box<[u32]>, i: usize) -> u32 {
    if i < b.len() {
        *b = Box::new([]);
        b[i]
    } else {
        0
    }
}

#[cfg(swapped)]
pub fn f(mut b: Box<[u32]>, c: Box<[u32]>, i: usize) -> u32 {
    if i < b.len() {
        b = c;
        b[i]
    } else {
        0
    }
}
