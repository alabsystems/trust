//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! W11 spawn census: `Builder::spawn_scoped` is a std thread spawn, identified
//! by std's diagnostic item rather than a printed path. Before, it matched no
//! spelling and carried no `UnmodeledThreadSpawnEffect` refusal. The call is
//! S1 in the closure. Since P2 (design 2026-09-29-spawn-census-by-construction)
//! the census walks `std::thread::scope::<{closure}>`, whose `catch_unwind`
//! runs the closure, so `scoped_builder` and `wrapper` are S2 SPAWNS rows (W11
//! refused them as UNKNOWNS: the closure handed to `scope` was an escaping
//! value).

#![allow(dead_code)]

pub fn scoped_builder() { //~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::thread::scope::<
    std::thread::scope(|s| { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
        let _ = std::thread::Builder::new().spawn_scoped(s, || {});
    });
}

pub fn wrapper() { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    scoped_builder();
}
