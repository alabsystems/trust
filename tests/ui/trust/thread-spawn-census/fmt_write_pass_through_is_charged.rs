//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:`UnmodeledThreadSpawnEffect`:
//! Spawn census (design 2026-09-29-spawn-census-by-construction §13, probe j02):
//! a pass-through frame. `l` hands a caller-created `&mut dyn fmt::Write` to
//! std's NON-generic `fmt::write`, which calls `write_str` through it. The
//! census walks `fmt::write` and charges that `dyn` call to the DynPool of
//! `dyn fmt::Write`, which holds `SpawnW::write_str` (created in `c` and
//! `direct`): `l` is INDIRECT, and the frames that create the trait object are
//! ESCAPES. `quiet`'s `write_str` does not spawn: no row.

#![allow(dead_code)]

use std::fmt;

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub struct SpawnW;

impl fmt::Write for SpawnW {
    fn write_str(&mut self, _: &str) -> fmt::Result { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops
        launch();
        Ok(())
    }
}

pub fn l(w: &mut dyn fmt::Write) { //[spawning]~ NOTE may spawn (indirect)
    let _ = fmt::write(w, format_args!("x"));
}

pub fn c() { //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn
    let mut s = SpawnW;
    l(&mut s);
}

pub fn direct() { //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn
    let mut s = SpawnW;
    let _ = fmt::write(&mut s, format_args!("y"));
}
