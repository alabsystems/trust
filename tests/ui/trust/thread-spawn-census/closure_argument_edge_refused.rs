//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census: a spawning closure handed to a local generic callee. Before
//! W11's body-level fallback `hands_off` carried NO spawn row while its caller
//! was refused; W11 then refused it as an UNKNOWN (a closure named as a value)
//! and its caller as an unknown too. Since P2 (design
//! 2026-09-29-spawn-census-by-construction) the census walks the instance
//! `run::<{closure}>`, which calls the closure exactly: `run`, `hands_off` and
//! `hands_off_caller` are S2 SPAWNS rows. `quiet` is the same shape with a
//! spawn-free closure: no spawn row may appear.

#![allow(dead_code)]

#[cfg(spawning)]
pub fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
pub fn launch() {}

#[inline(never)]
fn run<F: FnOnce()>(f: F) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops
    f()
}

pub fn hands_off() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via run::<
    run(|| launch());
}

pub fn hands_off_caller() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via hands_off → run::<
    hands_off();
}
