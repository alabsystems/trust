// Regression test for rust-lang#107975.
// Incorrect codegen for `*const dyn Fn()` transmute: the compiler could
// generate wrong LLVM IR when transmuting between raw pointers to trait
// objects, losing the vtable pointer or corrupting the data pointer.
//
// The bug manifested when transmuting `*const dyn Fn()` through an
// intermediate integer pair, then calling through the reconstructed
// trait object. The vtable dispatch would use a stale or zero pointer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ build-pass
//@ compile-flags: -C opt-level=2

#![allow(dead_code)]

use std::mem;

// A trait object pointer is a fat pointer: (data_ptr, vtable_ptr).
// Transmuting through (usize, usize) must preserve both components.
fn round_trip_via_usize_pair(f: *const dyn Fn() -> u32) -> *const dyn Fn() -> u32 {
    // SAFETY: *const dyn Fn() is a fat pointer with the same layout as (usize, usize).
    // This round-trip must be an identity operation.
    unsafe {
        let pair: (usize, usize) = mem::transmute(f);
        mem::transmute(pair)
    }
}

// Also test with Box<dyn Fn()> going through raw pointers.
fn box_round_trip(f: Box<dyn Fn() -> u32>) -> Box<dyn Fn() -> u32> {
    let raw: *mut dyn Fn() -> u32 = Box::into_raw(f);
    // SAFETY: pointer was just obtained from Box::into_raw.
    let raw2 = round_trip_via_usize_pair(raw as *const _) as *mut dyn Fn() -> u32;
    unsafe { Box::from_raw(raw2) }
}

struct Captured {
    value: u32,
}

fn main() {
    let c = Captured { value: 42 };
    let closure: Box<dyn Fn() -> u32> = Box::new(move || c.value);

    // Round-trip the trait object through usize pair transmutes.
    let recovered = box_round_trip(closure);
    assert_eq!(recovered(), 42);

    // Also test with a non-capturing closure via raw pointer round-trip.
    let bare_fn: fn() -> u32 = || 99;
    let trait_obj: Box<dyn Fn() -> u32> = Box::new(bare_fn);
    let recovered2 = box_round_trip(trait_obj);
    assert_eq!(recovered2(), 99);
}
