//@ revisions: checked unchecked
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[checked] compile-flags: -Zub-checks=yes
//@[unchecked] compile-flags: -Zub-checks=no
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[unchecked] forbid-output:core::panicking::panic_misaligned_pointer_dereference
//@[unchecked] forbid-output:core::panicking::panic_null_pointer_dereference
//@[unchecked] forbid-output:core::panicking::panic_invalid_enum_construction
//! Spawn census (P2 review, probe h14): the panics the optimization pipeline adds
//! AFTER the body the census reads. `CheckAlignment`, `CheckNull` and
//! `CheckEnums` open `run_optimization_pipeline`; they insert a panic before a
//! raw-pointer dereference (misaligned or null) and after a transmute into an
//! enum (an invalid discriminant). The census read the pre-steal body, which has
//! none of them, so with a spawning panic hook `read` and `to_e` were QUIET,
//! and the hook really ran (the probe's binary started a thread). The census now
//! runs the same three passes on its copy of each local body, exactly when the
//! pipeline runs them (`-Zub-checks`, `-Zmir-enable-passes`): under `checked`
//! both are INDIRECT through the hook; under `unchecked` no row cites those
//! panics.

#![allow(dead_code)]

fn launch() { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

pub fn install() { //~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn
    std::panic::set_hook(Box::new(|_| launch()));
}

pub fn read(p: *const u32) -> u32 { unsafe { *p } } //[checked]~ NOTE may spawn (indirect)

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum E {
    A = 0,
    B = 1,
}

pub fn to_e(x: u8) -> E { unsafe { std::mem::transmute::<u8, E>(x) } } //[checked]~ NOTE may spawn (indirect)
