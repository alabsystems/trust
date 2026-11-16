//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:UnmodeledThreadSpawnEffect
//! Control for `scope_spawn_refused_direct_and_through_wrapper.rs`:
//! `std::thread::scope` itself runs its closure on the calling thread and is
//! not a spawn entry point, so a scope that spawns nothing carries no spawn row.

#![allow(dead_code)]

pub fn scoped_quiet() -> u8 {
    std::thread::scope(|_s| 7)
}

pub fn wrapper() -> u8 {
    scoped_quiet()
}
