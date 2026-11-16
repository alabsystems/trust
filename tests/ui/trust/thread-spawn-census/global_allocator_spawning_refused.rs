//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:`UnmodeledThreadSpawnEffect`:
//! Spawn census (design 2026-09-29-spawn-census-by-construction §13, probe j04):
//! a spawning `#[global_allocator]`. Every allocation reaches it through
//! alloc's FOREIGN `__rust_alloc`, never through a call that names it. The
//! census resolves that foreign symbol by link name to the `__rust_alloc` the
//! `#[global_allocator]` expansion defines here, so `boxit` reaches the spawn
//! over calls only: a SPAWNS row (S2), through std's own `Box::new`. `quiet`
//! has a spawn-free allocator: no row.

#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout, System};

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub struct A;

unsafe impl GlobalAlloc for A {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops
        launch();
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static G: A = A;

pub fn boxit() -> Box<u64> { //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    Box::new(7)
}
