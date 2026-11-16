//@ revisions: alloc hook kept minted plain
//@ aux-build:mirless_dep.rs
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[plain] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (P2 review, probes h19, h21, h13): a dependency function with no
//! MIR (R2) is assumed to start no thread ITSELF, but it can reach the crate's
//! runtime registries without being handed them, keep what it is handed, and
//! hand back a callable it minted. Each was QUIET, and each really spawned:
//!
//! * `alloc`: `make_string` allocates through a spawning `#[global_allocator]`;
//! * `hook`: `checked` panics into a spawning panic hook;
//! * `kept`: `register` keeps the spawner `reg` hands it, and `run` calls it;
//! * `minted`: `get` returns a pointer to an `#[inline]` spawner, and `get_dyn` a
//!   vtable whose generic method spawns, neither recorded by any pool.
//!
//! Every MIR-less Rust body now runs the Rust world's node: it may call the
//! allocator, the alloc error handler and the panic handler, and everything any
//! frame outside the sysroot handed code with no body (the first three are
//! INDIRECT). A MIR-less function whose signature can carry a callable out is
//! UNKNOWN (the fourth). `plain` calls the same functions with nothing that
//! spawns: no row.

#![allow(dead_code)]

extern crate mirless_dep;

#[cfg(not(plain))]
fn launch() {
    let _handle = std::thread::spawn(|| {});
}

#[cfg(alloc)]
mod allocator {
    use std::alloc::{GlobalAlloc, Layout, System};

    pub struct A;
    unsafe impl GlobalAlloc for A {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            super::launch();
            unsafe { System.alloc(layout) }
        }
        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            unsafe { System.dealloc(ptr, layout) }
        }
    }

    #[global_allocator]
    static G: A = A;
}

pub fn via_dep_alloc() -> usize { std::mem::forget(mirless_dep::make_string(3)); 0 } //[alloc]~ NOTE may spawn (indirect)

#[cfg(hook)]
pub fn install() { std::panic::set_hook(Box::new(|_| launch())); }

pub fn via_dep_panic(v: &[u8]) -> u8 { mirless_dep::checked(v, 9) } //[hook]~ NOTE may spawn (indirect)

#[cfg(kept)]
pub fn reg() { mirless_dep::register(launch) } //[kept]~ NOTE may spawn (indirect)

pub fn run() { mirless_dep::run() } //[kept]~ NOTE may spawn (indirect)

#[cfg(minted)]
pub fn fire() { mirless_dep::get()() } //[minted]~ NOTE not enumerated (no spawn was found)

#[cfg(minted)]
pub fn fire_dyn() { mirless_dep::get_dyn().run() } //[minted]~ NOTE not enumerated (no spawn was found)
