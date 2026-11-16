//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (P2 review, probe h1): core's fn-pointer documentation makes a
//! call through an `extern "C-unwind"` pointer of an `extern "C"` function
//! ABI-compatible, so it is not UB (R4). FnPool keys hashed the ABI string
//! exactly, so `fire` (a union field) and `fire_ptr` (a pointer cast) met an
//! empty pool and were QUIET, and both really spawned. A `$X-unwind` convention
//! now shares `$X`'s class: both are INDIRECT. `quiet`: no row.

#![allow(dead_code)]

#[cfg(spawning)]
pub extern "C" fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
pub extern "C" fn launch() {}

#[repr(C)]
pub union U {
    pub a: extern "C" fn(),
    pub b: extern "C-unwind" fn(),
}

pub fn make() -> U { U { a: launch } } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called

pub fn fire(u: U) { unsafe { (u.b)() } } //[spawning]~ NOTE may spawn (indirect)

pub fn fire_ptr(p: *const extern "C" fn()) { //[spawning]~ NOTE may spawn (indirect)
    let q = p as *const extern "C-unwind" fn();
    unsafe { (*q)() }
}
