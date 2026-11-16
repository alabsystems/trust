//@ revisions: walked plain
//@ aux-build:spawning_dep.rs
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[plain] forbid-output:`UnmodeledThreadSpawnEffect`:
//! Spawn census (design 2026-09-29-spawn-census-by-construction §5.3, §12,
//! §13, probe p03): another crate's bodies are walked from metadata when they
//! have MIR. A generic or `#[inline]` dependency function that spawns is a
//! SPAWNS row at the call (S2). A non-generic dependency function has no MIR
//! in its metadata (without `-Zalways-encode-mir`), so it is opaque: assumed
//! quiet apart from rule H. That is exclusion R2, disclosed in
//! docs/KNOWN_HAZARDS.md and filed for the owner in docs/DECISION_QUEUE.md;
//! the `plain` revision pins it (no row), so a change to R2 shows up here.

#![allow(dead_code)]

extern crate spawning_dep;

#[cfg(walked)]
pub fn calls_generic() { //[walked]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    spawning_dep::spawn_generic(1u8)
}

#[cfg(walked)]
pub fn calls_inline() { //[walked]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    spawning_dep::spawn_inline()
}

pub fn calls_plain() {
    spawning_dep::spawn_plain()
}
