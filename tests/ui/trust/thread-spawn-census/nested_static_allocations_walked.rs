//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (P2 review, drop-in): a `static` whose initializer takes a
//! mutable reference interns the referenced memory as a NESTED static, a
//! synthetic definition with no type. The census asked `type_of` of every
//! static it walked and ICEd ("unexpected sort of node in type_of(): Synthetic")
//! on valid Rust in the verified lane, including seven upstream run-pass tests
//! (`consts/static-mut-refs`, `statics/nested_struct`, ...). A nested static is
//! reached, and written, only through its parent static, whose type the census
//! names; its allocation is still walked: `entry` reads `TABLE`, whose nested
//! allocation holds `launch` (ESCAPES), and `fire` calls what it returns (INDIRECT).
//! `quiet`: no row.

#![allow(dead_code)]
#![allow(static_mut_refs)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

static mut BYTES: &mut [u8] = &mut [1, 2];

pub fn first() -> u8 { unsafe { BYTES[0] } }

static mut TABLE: &mut [fn()] = &mut [launch];

fn entry() -> fn() { unsafe { TABLE[0] } }

pub fn fire() { let f = entry(); f() } //[spawning]~ NOTE callee names, erases or reads a callable that reaches a std thread spawn
//[spawning]~^ NOTE may spawn (indirect)
