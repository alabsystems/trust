//@ revisions: link_name plain_name map_closure verbatim_import verbatim_definer dependency global_asm
//@ aux-build:foreign_symbol_definer_dep.rs
//@[verbatim_import] only-macos
//@[global_asm] only-macos
//@[global_asm] only-aarch64
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A foreign import (`extern` block item) whose link symbol THIS crate defines is
//! not the libc function its name suggests: the body that runs is the local
//! `#[no_mangle] extern "C" fn`, proved only under its `requires`, which the call
//! never establishes. Review round 19 of 2026-09-30 measured each revision building
//! rc=0 under certify (the FFI summary db, keyed on the Rust declaration name, gave
//! the `close` import libc's demand-free summary) while the caller aborted on
//! index 15 of a 10-element table. The call is now unresolved, so the caller is
//! refused.
//!
//! `verbatim_import` / `verbatim_definer`: a `\x01` prefix makes a name verbatim, so
//! `\x01_my_close` is the Mach-O linker symbol of `my_close`; review round 20
//! certified both directions against a raw string compare. Linker symbols are now
//! compared. `dependency`: a dependency that exports the symbol answers the import
//! too (round 20, both crates certified and the program aborted). `global_asm`: an
//! assembly label defines the symbol (round 21); any `global_asm!` in the crate now
//! makes every foreign import unresolved. A DEPENDENCY's asm label stays invisible
//! (docs/KNOWN_HAZARDS.md, OPEN).

static T: [i32; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

#[cfg(any(link_name, map_closure))]
#[no_mangle]
pub extern "C" fn my_close(fd: i32) -> i32
    requires fd >= 0 && fd < 10
{
    T[fd as usize]
}
#[cfg(any(link_name, map_closure))]
unsafe extern "C" {
    #[link_name = "my_close"]
    safe fn close(fd: i32) -> i32;
}
#[cfg(link_name)]
pub fn caller(fd: i32) -> i32 { close(fd) } //[link_name]~ ERROR verification failed
#[cfg(map_closure)]
pub fn caller(fd: i32) -> Option<i32> { Some(fd).map(|x| close(x)) } //[map_closure]~ ERROR verification failed

#[cfg(plain_name)]
pub mod imp {
    #[no_mangle]
    pub extern "C" fn close(fd: i32) -> i32
        requires fd >= 0 && fd < 10
    {
        super::T[fd as usize]
    }
}
#[cfg(plain_name)]
mod sys {
    unsafe extern "C" {
        pub safe fn close(fd: i32) -> i32;
    }
}
#[cfg(plain_name)]
pub fn caller(fd: i32) -> i32 { sys::close(fd) } //[plain_name]~ ERROR verification failed

#[cfg(verbatim_import)]
#[no_mangle]
pub extern "C" fn my_close(fd: i32) -> i32
    requires fd >= 0 && fd < 10
{
    T[fd as usize]
}
#[cfg(verbatim_import)]
unsafe extern "C" {
    #[link_name = "\x01_my_close"]
    safe fn close(fd: i32) -> i32;
}
#[cfg(verbatim_import)]
pub fn caller(fd: i32) -> i32 { close(fd) } //[verbatim_import]~ ERROR verification failed

#[cfg(verbatim_definer)]
#[export_name = "\x01close_impl_verbatim"]
pub extern "C" fn my_close(fd: i32) -> i32
    requires fd >= 0 && fd < 10
{
    T[fd as usize]
}
#[cfg(verbatim_definer)]
unsafe extern "C" {
    #[link_name = "\x01close_impl_verbatim"]
    safe fn close(fd: i32) -> i32;
}
#[cfg(verbatim_definer)]
pub fn caller(fd: i32) -> i32 { close(fd) } //[verbatim_definer]~ ERROR verification failed

#[cfg(dependency)]
extern crate foreign_symbol_definer_dep;
#[cfg(dependency)]
unsafe extern "C" {
    #[link_name = "dep_close"]
    safe fn close(fd: i32) -> i32;
}
#[cfg(dependency)]
pub fn caller(fd: i32) -> i32 { close(fd) } //[dependency]~ ERROR verification failed

#[cfg(global_asm)]
#[no_mangle]
pub extern "C" fn inner_close(fd: i32) -> i32
    requires fd >= 0 && fd < 10
{
    T[fd as usize]
}
#[cfg(global_asm)]
core::arch::global_asm!(".globl _close", "_close:", "b _inner_close");
#[cfg(global_asm)]
unsafe extern "C" {
    safe fn close(fd: i32) -> i32;
}
#[cfg(global_asm)]
pub fn caller(fd: i32) -> i32 { close(fd) } //[global_asm]~ ERROR verification failed
