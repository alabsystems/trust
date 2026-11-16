//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:`UnmodeledThreadSpawnEffect`:
//! Spawn census (design 2026-09-29-spawn-census-by-construction §13, probe j03):
//! core's NON-generic `Waker::wake` calls a fn pointer stored in a static
//! `RawWakerVTable`; nothing on `fire`'s stack created it. The census walks
//! `Waker::wake` (std has MIR), charges its fn-pointer call to the FnPool of
//! that shape, and finds `wake` there: `VTABLE`'s evaluated allocation holds
//! it. `fire` is INDIRECT; `make`, which reads `VTABLE`, is ESCAPES. `quiet`
//! has a spawn-free `wake`: no row.

#![allow(dead_code)]

use std::task::{RawWaker, RawWakerVTable, Waker};

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

unsafe fn clone(p: *const ()) -> RawWaker {
    RawWaker::new(p, &VTABLE)
}
unsafe fn wake(_: *const ()) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops
    launch()
}
unsafe fn wake_by_ref(_: *const ()) {}
unsafe fn drop_waker(_: *const ()) {}

static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, wake, wake_by_ref, drop_waker);

pub fn make() -> Waker { //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
    unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
}

pub fn fire(w: Waker) { //[spawning]~ NOTE may spawn (indirect)
    w.wake()
}
