//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:`UnmodeledThreadSpawnEffect`:
//! Spawn census (design 2026-09-29-spawn-census-by-construction §5.4, §13):
//! indirect calls are refused where they are CALLED, through their pool.
//!
//! * FnPool, keyed by call shape: `call_ptr` (a `fn()` call) may run `launch`,
//!   which `reify` turns into a `fn()`; `call_u8` (a `fn(u8)` call) may not.
//! * DynPool, keyed by principal and method: `call_job` may run `Loud::run`,
//!   which `erase_loud` erases to `dyn Job`; `call_calm` reaches only
//!   `Still::calm`.
//! * DynDropPool (probe p01): dropping a `Box<dyn Any>` may run the drop glue of
//!   any type erased to `dyn Any` through an owning pointer: `DropSpawner`'s, in
//!   `box_any` (which takes the box: `Box::new(DropSpawner)` would itself be S2,
//!   since `Box::new` drops its argument if the allocation panics). A vtable minted through a shared `&` joins the pool without a
//!   CREATE edge (the `&`-erasure rule): `borrow_any` is quiet.
//!
//! The calling frames are INDIRECT and the creating frames ESCAPES; neither is
//! a spawn claim. `quiet` has the same shapes with nothing that spawns.

#![allow(dead_code)]

use std::any::Any;

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

fn quiet_u8(_: u8) {}

pub fn reify() -> fn() { //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn
    launch
}
pub fn reify_u8() -> fn(u8) {
    quiet_u8
}
pub fn call_ptr(f: fn()) { //[spawning]~ NOTE may spawn (indirect)
    f()
}
pub fn call_u8(f: fn(u8)) {
    f(1)
}

pub trait Job {
    fn run(&self);
}
pub struct Loud;
impl Job for Loud {
    fn run(&self) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops
        launch()
    }
}
pub trait Calm {
    fn calm(&self);
}
pub struct Still;
impl Calm for Still {
    fn calm(&self) {}
}
pub fn erase_loud(l: &'static Loud) -> &'static dyn Job { //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn
    l
}
pub fn call_job(j: &dyn Job) { //[spawning]~ NOTE may spawn (indirect)
    j.run()
}
pub fn erase_still(s: &'static Still) -> &'static dyn Calm {
    s
}
pub fn call_calm(c: &dyn Calm) {
    c.calm()
}

pub struct DropSpawner;
impl Drop for DropSpawner {
    fn drop(&mut self) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops
        launch()
    }
}
pub fn box_any(b: Box<DropSpawner>) -> Box<dyn Any> { //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn
    b
}
pub fn drop_any(b: Box<dyn Any>) { //[spawning]~ NOTE may spawn (indirect)
    let _ = b;
}
pub fn borrow_any(d: &DropSpawner) -> &dyn Any {
    d
}
