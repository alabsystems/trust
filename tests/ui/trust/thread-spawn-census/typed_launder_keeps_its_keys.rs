//@ revisions: same_shape other_shape object object_control vec_stored
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[other_shape] forbid-output:may spawn (indirect): an indirect call
//@[other_shape] forbid-output:may spawn (indirect): the callee
//@[object_control] forbid-output:may spawn (indirect): an indirect call
//@[object_control] forbid-output:may spawn (indirect): the callee
//! Spawn census, typed LAUNDER (design §10): a pun's LAUNDER is keyed by the
//! callables the reinterpreted bytes may hold, by shape, so plain data holds
//! only callables of a shape some pun put there. `launch` (`fn()`) spawns and
//! `keep` makes it a fn pointer; `hand` gives an integer to C, which may call
//! it back. `pun` reads a callable that does not spawn as an integer:
//!
//! * `same_shape`: a `fn()`. Keys are shapes, not callables, so data may hold
//!   `launch` too: `hand` is INDIRECT.
//! * `other_shape`: a `fn(u8)`. No zero-argument callable is in data: `hand`
//!   is QUIET.
//! * `object`: a `&dyn Fn()` read through a thin `*const usize`. The view
//!   reads the concrete closure's own bytes, which hold a `fn()`: INDIRECT.
//! * `object_control`: the same with a closure that captures no fn pointer:
//!   its bytes hold no callable, and a vtable word is no callable in data
//!   (SC-7c): QUIET.
//! * `vec_stored`: a `fn()` stored in a `Vec`: RawVec keeps its elements
//!   behind a `*mut u8` and reads them through a `*mut T` derived from it, a
//!   pointer view at another pointee, so every element shape stored in a
//!   `Vec` is in data. The documented cost of shape granularity: INDIRECT.

#![allow(dead_code)]

extern "C" {
    fn c_call_back(n: usize);
}

fn launch() {
    let _handle = std::thread::spawn(|| {});
}

pub fn keep() -> fn() {
    launch
}

#[cfg(any(same_shape, vec_stored))]
fn seed() {}

#[cfg(other_shape)]
fn seed(_: u8) {}

#[cfg(same_shape)]
pub fn pun() -> usize {
    let f: fn() = seed;
    unsafe { *(&f as *const fn() as *const usize) }
}

#[cfg(other_shape)]
pub fn pun() -> usize {
    let f: fn(u8) = seed;
    unsafe { *(&f as *const fn(u8) as *const usize) }
}

#[cfg(object)]
pub fn pun() -> usize {
    fn quiet() {}
    let g: fn() = quiet;
    let c = move || g();
    let d: &dyn Fn() = &c;
    unsafe { *(d as *const dyn Fn() as *const usize) }
}

#[cfg(object_control)]
pub fn pun() -> usize {
    let c = move || 7u32;
    let d: &dyn Fn() -> u32 = &c;
    unsafe { *(d as *const dyn Fn() -> u32 as *const usize) }
}

#[cfg(vec_stored)]
pub fn store() -> Vec<fn()> {
    vec![seed]
}

pub fn hand(n: usize) {
    //[same_shape,object,vec_stored]~^ NOTE may spawn (indirect)
    unsafe { c_call_back(n) }
}
