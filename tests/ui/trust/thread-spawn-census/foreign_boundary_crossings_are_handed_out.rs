//@ revisions: returned argument returned_to_c by_value data
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[by_value] forbid-output:may spawn (indirect): the callee
//@[data] forbid-output:may spawn (indirect): the callee
//! Spawn census: besides a call's operands (rule H) and memory it names
//! (`extern` and exported statics), a callable reaches foreign code through
//! memory the two sides share by pointer, with no static named:
//! * `returned`: a store through a pointer foreign code returned (its
//!   registration slot);
//! * `argument`: a store through a pointer foreign code passed to a Rust body
//!   with a foreign calling convention;
//! * `returned_to_c`: such a body returns foreign code a pointer to memory Rust
//!   fills later.
//! What that memory can be made to hold is charged to the foreign world, so
//! `run`, which hands C nothing, is INDIRECT. Controls, QUIET: `by_value` (a
//! struct of fn pointers returned by value: storing into the copy hands
//! nothing) and `data` (a byte pointer, and no LAUNDER in the crate).
//! `make` mints the spawner into the pool of `extern "C" fn()`.

#![allow(dead_code, static_mut_refs, improper_ctypes, improper_ctypes_definitions)]

fn launch() {
    let _handle = std::thread::spawn(|| {});
}

pub extern "C" fn c_launch() {
    launch()
}

pub fn make() -> extern "C" fn() {
    c_launch
}

unsafe extern "C" {
    safe fn trust_census_run();
}

#[cfg(returned)]
unsafe extern "C" {
    fn trust_census_slot() -> *mut Option<extern "C" fn()>;
}

#[cfg(returned)]
pub fn register(f: extern "C" fn()) {
    unsafe { *trust_census_slot() = Some(f) }
}

#[cfg(any(argument, returned_to_c))]
static mut CB: Option<extern "C" fn()> = None;

#[cfg(any(argument, returned_to_c))]
pub fn setup(f: extern "C" fn()) {
    unsafe { CB = Some(f) }
}

#[cfg(argument)]
#[repr(C)]
pub struct Ops {
    pub cb: Option<extern "C" fn()>,
}

#[cfg(argument)]
#[unsafe(no_mangle)]
pub extern "C" fn trust_census_init(ops: *mut Ops) {
    unsafe { (*ops).cb = CB }
}

#[cfg(returned_to_c)]
#[unsafe(no_mangle)]
pub extern "C" fn trust_census_slot_addr() -> *mut Option<extern "C" fn()> {
    &raw mut CB
}

#[cfg(by_value)]
#[repr(C)]
pub struct Ops {
    pub cb: Option<extern "C" fn()>,
}

#[cfg(by_value)]
unsafe extern "C" {
    fn trust_census_ops() -> Ops;
}

#[cfg(by_value)]
pub fn copy(f: extern "C" fn()) {
    let mut ops = unsafe { trust_census_ops() };
    ops.cb = Some(f);
}

#[cfg(data)]
unsafe extern "C" {
    fn trust_census_buf() -> *mut u8;
}

#[cfg(data)]
pub fn fill() {
    unsafe { *trust_census_buf() = 1 }
}

pub fn run() { //[returned,argument,returned_to_c]~ NOTE may spawn (indirect)
    trust_census_run()
}
