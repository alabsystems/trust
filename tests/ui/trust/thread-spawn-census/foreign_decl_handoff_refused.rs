//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (W11 round 4): a value handed to a LOCAL FOREIGN declaration.
//! `callee_observes_its_drops` skipped every call that resolved to a local,
//! non-generic `InstanceKind::Item`, on the ground that the callee's own census
//! body classifies its drops. A foreign declaration (`extern "C"` or
//! `extern "Rust"`) meets all three conditions but has NO MIR, so nothing ever
//! observed what its definition — another crate's `#[no_mangle] fn rust_take(o:
//! &mut Option<Spawner>) { *o = None }` — drops: `unsafe { rust_take(o) }` and
//! every safe caller carried no `UnmodeledThreadSpawnEffect` row, while the
//! same hand-off through an fn pointer or `ptr::drop_in_place` was refused
//! (review probes s4.rs / s5.rs, 2026-09-29). A foreign declaration is now a
//! callee whose body the census cannot see. Since P2 (design
//! 2026-09-29-spawn-census-by-construction §5.4, rule H) code with no body
//! (foreign, R3; an `extern "Rust"` declaration's definition is Rust) invokes
//! every pool key, and may drop what it is handed by value, `&mut` or raw
//! pointer: an ESCAPES row ("value handed here to code the spawn census cannot
//! walk"), and its callers ESCAPES, never a spawn claim (W11: an UNKNOWN).
//! `quiet` has a spawn-free `Drop`: no row.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub struct Spawner;
impl Drop for Spawner {
    fn drop(&mut self) { launch() } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
}

extern "C" {
    fn ext_take(p: *mut Option<Spawner>);
}
extern "Rust" {
    fn rust_take(o: &mut Option<Spawner>);
}

pub fn c_foreign(o: &mut Option<Spawner>) { unsafe { ext_take(o) } } //[spawning]~ NOTE value handed here to code the spawn census cannot walk (foreign or MIR-less) has drop glue that reaches a std thread spawn
pub fn c_caller(o: &mut Option<Spawner>) { c_foreign(o) } //[spawning]~ NOTE callee names, erases or reads a callable that reaches a std thread spawn

pub fn rust_foreign(o: &mut Option<Spawner>) { unsafe { rust_take(o) } } //[spawning]~ NOTE value handed here to code the spawn census cannot walk (foreign or MIR-less) has drop glue that reaches a std thread spawn
pub fn rust_caller(o: &mut Option<Spawner>) { rust_foreign(o) } //[spawning]~ NOTE callee names, erases or reads a callable that reaches a std thread spawn

// A foreign declaration handed nothing droppable observes nothing.
extern "C" {
    fn ext_len(n: usize) -> usize;
}
pub fn quiet_foreign(n: usize) -> usize { unsafe { ext_len(n) } }
