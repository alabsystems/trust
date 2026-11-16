//@ revisions: no_mangle export_name link_section mutable pointee dep used_only private data quiet
//@[dep] aux-build:exported_static_dep.rs
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[used_only] forbid-output:may spawn (indirect): the callee
//@[private] forbid-output:may spawn (indirect): the callee
//@[data] forbid-output:may spawn (indirect): the callee
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census: foreign code reads a static it names by symbol or section
//! without being handed it (P4 review probe a07: a linked C caller spawned a
//! thread from `run`). The static's value is a member of the foreign world's
//! pool (foreign code may call what its walked contents hold), and what Rust
//! may store in it later, or behind its pointers, is handed to the foreign
//! world, so `run`, which hands C nothing, is INDIRECT:
//! * `no_mangle`, `export_name`: exported, holding a spawner;
//! * `link_section`: in a named section, its symbol private;
//! * `mutable`: an exported `static mut`, filled later;
//! * `pointee`: an exported immutable static holding a pointer to a private
//!   `static mut` that is filled later;
//! * `dep`: a dependency exports one (no local body names it).
//! Controls, QUIET: `used_only` (`#[used]` keeps the static but gives foreign
//! code no name for it), `private` (a mangled static), `data` (an exported
//! static of plain data, and no LAUNDER in the crate), and `quiet` (the
//! callable starts no thread).

#![allow(dead_code, static_mut_refs, improper_ctypes, improper_ctypes_definitions)]

#[cfg(dep)]
extern crate exported_static_dep;

#[cfg(not(quiet))]
fn launch() {
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub extern "C" fn c_launch() {
    launch()
}

#[cfg(data)]
pub fn make() -> extern "C" fn() {
    c_launch
}

unsafe extern "C" {
    safe fn trust_census_run();
}

#[cfg(any(no_mangle, quiet))]
#[unsafe(no_mangle)]
pub static TRUST_CENSUS_CALLBACK: extern "C" fn() = c_launch;

#[cfg(export_name)]
#[unsafe(export_name = "trust_census_cb")]
pub static CB: extern "C" fn() = c_launch;

#[cfg(link_section)]
#[used]
#[cfg_attr(target_vendor = "apple", unsafe(link_section = "__DATA,__trust_cbs"))]
#[cfg_attr(not(target_vendor = "apple"), unsafe(link_section = "trust_census_cbs"))]
static CB: extern "C" fn() = c_launch;

#[cfg(mutable)]
#[unsafe(no_mangle)]
pub static mut TRUST_CENSUS_SLOT: Option<extern "C" fn()> = None;

#[cfg(mutable)]
pub fn fill() {
    unsafe { TRUST_CENSUS_SLOT = Some(c_launch) }
}

#[cfg(pointee)]
static mut PRIVATE: Option<extern "C" fn()> = None;

#[cfg(pointee)]
pub struct Ptr(*mut Option<extern "C" fn()>);

#[cfg(pointee)]
unsafe impl Sync for Ptr {}

#[cfg(pointee)]
#[unsafe(no_mangle)]
pub static TRUST_CENSUS_PTR: Ptr = Ptr(&raw mut PRIVATE);

#[cfg(pointee)]
pub fn fill() {
    unsafe { PRIVATE = Some(c_launch) }
}

#[cfg(used_only)]
#[used]
static KEEP: extern "C" fn() = c_launch;

#[cfg(private)]
pub static CB: extern "C" fn() = c_launch;

#[cfg(data)]
#[unsafe(no_mangle)]
pub static TRUST_CENSUS_VERSION: u32 = 3;

pub fn run() { //[no_mangle,export_name,link_section,mutable,pointee,dep]~ NOTE may spawn (indirect)
    trust_census_run()
}
