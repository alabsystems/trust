//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (W11 round 2): a spawning fn item reified inside a PROMOTED
//! constant. `&(launch as fn())` is lifted into `promoted[0]`, so the body's
//! own MIR holds only a constant of type `&fn()` and, before W11, the census
//! had no edge and no row; W11 refused the naming body as an UNKNOWN. Since P2
//! (design 2026-09-29-spawn-census-by-construction §5.3) a promoted is a value
//! node whose MIR (`promoted_mir`) is walked: its reification is a CREATE, and
//! the body that uses the promoted READs it, an ESCAPES row ("const or static
//! read here holds a callable"); a call through it is INDIRECT too. `quiet` is
//! the same shapes with a spawn-free `launch`: no spawn row may appear.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub fn promoted_reified() { let f: &'static fn() = &(launch as fn()); f() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

pub fn promoted_tuple() { let t: &'static (u8, fn()) = &(1u8, launch as fn()); (t.1)() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

pub fn promoted_array() -> &'static [fn(); 1] { &[launch as fn()] } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
