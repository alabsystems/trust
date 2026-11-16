//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:`UnmodeledThreadSpawnEffect`:
//! Spawn census (design 2026-09-29-spawn-census-by-construction §13, probe p04):
//! a spawning panic hook. No call names the hook: std's panic handler calls it
//! through the `Box<dyn Fn(&PanicHookInfo) + Sync + Send>` that `set_hook`
//! stored, so the census reaches it only because it resolves the foreign
//! `panic_impl` to std's panic handler, walks it, and charges the hook call to
//! its DynPool, which holds the closure `install` created. Every function that
//! can panic is then INDIRECT ("may spawn (indirect)"), and `install` itself,
//! which only creates the hook, is ESCAPES. Neither is a spawn claim. `quiet`
//! installs a hook that does not spawn: no row anywhere.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub fn install() { //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn
    std::panic::set_hook(Box::new(|_| launch()));
}

pub fn first(v: &[u8]) -> u8 { //[spawning]~ NOTE may spawn (indirect)
    v[0]
}

pub fn explicit(ok: bool) { //[spawning]~ NOTE may spawn (indirect)
    if !ok {
        panic!("explicit");
    }
}
