//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (P2 review, probe h20): foreign code may KEEP a callback it is
//! handed and call it from a later, unrelated call (C's register/run pattern).
//! Rule H charges only the frame that hands the callback over (`register`), so
//! `run`, which hands nothing, was QUIET, and the callback really spawned. Every
//! call into foreign code now reaches the foreign world's node, which holds
//! whatever any frame outside the sysroot ever handed such code: `run` is
//! INDIRECT. `quiet`: the callback starts no thread, no row.

#![allow(dead_code)]

use std::ffi::c_void;

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

extern "C" fn launch_cb(_data: *mut c_void) { launch() } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops

#[repr(C)]
pub struct Ops {
    pub cb: extern "C" fn(*mut c_void),
    pub data: *mut c_void,
}

pub fn make_ops() -> Ops { Ops { cb: launch_cb, data: std::ptr::null_mut() } } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called

unsafe extern "C" {
    fn c_register(ops: *const Ops);
    fn c_run();
}

pub fn register(ops: &Ops) { unsafe { c_register(ops) } } //[spawning]~ NOTE may spawn (indirect)

pub fn run() { unsafe { c_run() } } //[spawning]~ NOTE may spawn (indirect)
