//@ revisions: direct by_address interior pointee initializer tls dep read_only data quiet
//@[dep] aux-build:foreign_static_dep.rs
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[read_only] forbid-output:may spawn (indirect): the callee
//@[data] forbid-output:may spawn (indirect): the callee
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census: foreign code reads an `extern` static without being handed it
//! (P4 review probe a08: a linked C caller spawned a thread from `run`). What a
//! Rust frame stores there, or behind the pointers it holds, foreign code may
//! call during any later call into it, as a callback it was handed. The census
//! charges the static's type (what Rust may store there) to the foreign world
//! where a walked node names its address, so `run`, which hands C nothing, is
//! INDIRECT in every revision that stores a callable:
//! * `direct`: a store into a `static mut`;
//! * `by_address`: through `&raw mut` and a helper (the charge sits where the
//!   address is named, not where it is written);
//! * `interior`: through a `Cell` in an immutable static (its bytes are
//!   writable: not `Freeze`);
//! * `pointee`: through a pointer an immutable static holds;
//! * `initializer`: through a pointer another static's initializer holds;
//! * `tls`: a thread-local `extern` static;
//! * `dep`: a dependency's `#[inline]` body stores into its own.
//! Controls, QUIET: `read_only` (immutable `Freeze` bytes with no pointer:
//! writing them is UB), `data` (plain data, and no LAUNDER in the crate), and
//! `quiet` (the stored callable starts no thread).
//! `make` mints the spawner into the pool of `extern "C" fn()` in every
//! revision, so a missing or an extra charge shows on `run`.

#![cfg_attr(tls, feature(thread_local))]
#![allow(dead_code, static_mut_refs, improper_ctypes, improper_ctypes_definitions)]

#[cfg(dep)]
extern crate foreign_static_dep;

#[cfg(not(quiet))]
fn launch() {
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub extern "C" fn c_launch() {
    launch()
}

pub fn make() -> extern "C" fn() {
    c_launch
}

unsafe extern "C" {
    safe fn trust_census_run();
}

#[cfg(any(direct, by_address, initializer, quiet))]
unsafe extern "C" {
    static mut HOOK: Option<extern "C" fn()>;
}

#[cfg(any(direct, quiet))]
pub fn register(f: extern "C" fn()) {
    unsafe { HOOK = Some(f) }
}

#[cfg(by_address)]
fn put(slot: *mut Option<extern "C" fn()>, f: extern "C" fn()) {
    unsafe { *slot = Some(f) }
}

#[cfg(by_address)]
pub fn register(f: extern "C" fn()) {
    put(&raw mut HOOK, f)
}

#[cfg(interior)]
unsafe extern "C" {
    static CELL: std::cell::Cell<Option<extern "C" fn()>>;
}

#[cfg(interior)]
pub fn register(f: extern "C" fn()) {
    unsafe { CELL.set(Some(f)) }
}

#[cfg(pointee)]
unsafe extern "C" {
    static SLOT: *mut Option<extern "C" fn()>;
}

#[cfg(pointee)]
pub fn register(f: extern "C" fn()) {
    unsafe { *SLOT = Some(f) }
}

#[cfg(initializer)]
struct Slot(*mut Option<extern "C" fn()>);

#[cfg(initializer)]
unsafe impl Sync for Slot {}

#[cfg(initializer)]
static P: Slot = Slot(&raw mut HOOK);

#[cfg(initializer)]
pub fn register(f: extern "C" fn()) {
    unsafe { *P.0 = Some(f) }
}

#[cfg(tls)]
unsafe extern "C" {
    #[thread_local]
    static mut TLS_HOOK: Option<extern "C" fn()>;
}

#[cfg(tls)]
pub fn register(f: extern "C" fn()) {
    unsafe { TLS_HOOK = Some(f) }
}

#[cfg(dep)]
pub fn register(f: extern "C" fn()) {
    foreign_static_dep::register(f)
}

#[cfg(read_only)]
unsafe extern "C" {
    static TABLE: [extern "C" fn(); 2];
    static VERSION: [u8; 8];
}

#[cfg(read_only)]
pub fn read() -> (extern "C" fn(), u8) {
    unsafe { (TABLE[0], VERSION[0]) }
}

#[cfg(data)]
unsafe extern "C" {
    static mut COUNTER: u32;
}

#[cfg(data)]
pub fn bump() {
    unsafe { COUNTER += 1 }
}

pub fn run() { //[direct,by_address,interior,pointee,initializer,tls,dep]~ NOTE may spawn (indirect)
    trust_census_run()
}
