//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! W11 spawn census: `Scope::spawn` inside `std::thread::scope` is a std thread
//! spawn. The matcher used to spell entry points as untrimmed def paths; the
//! inherent impl of the generic `Scope<'scope, 'env>` prints its generic
//! arguments, so `s.spawn(..)` matched no row and NO `UnmodeledThreadSpawnEffect`
//! refusal appeared anywhere. Identity is now std's diagnostic item. The
//! refusal must reach the spawning closure (S1), the fn that hands it to
//! `thread::scope`, and every local wrapper above it. W11 refused those above
//! the closure as UNKNOWNS (a closure handed on as a value). Since P2 (design
//! 2026-09-29-spawn-census-by-construction) the census walks
//! `std::thread::scope::<{closure}>`, whose `catch_unwind` runs the closure
//! (the intrinsic's `do_call::<F, R>` operand is that one fn item), so the fn
//! that calls `scope` and every wrapper above it are S2 SPAWNS rows.

#![allow(dead_code)]

pub fn scoped() { //~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::thread::scope::<
    std::thread::scope(|s| { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
        s.spawn(|| {});
    });
}

pub fn wrapper() { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    scoped();
}

pub fn outer_wrapper() { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    wrapper();
}
