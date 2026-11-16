//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! W11 spawn census, companion to `scope_spawn_refused_direct_and_through_wrapper.rs`:
//! the diagnostic-item identity of `Scope::spawn` / `Builder::spawn_scoped` must
//! hold in a nested scope, in a local helper that receives the `&Scope`, and
//! when the method is called by fully qualified path. Each spawning body is a
//! direct site (S1); each fn or closure above it carries an S2 row: where it
//! calls the spawning helper, and (since P2, design
//! 2026-09-29-spawn-census-by-construction) where it hands a spawning closure
//! to `std::thread::scope`, whose instance runs it through `catch_unwind`. W11
//! refused the latter as UNKNOWNS (an escaping value).

#![allow(dead_code)]

use std::thread::{Builder, Scope};

pub fn nested_scopes() { //~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::thread::scope::<
    std::thread::scope(|_a| { //~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::thread::scope::<
        std::thread::scope(|b| { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
            b.spawn(|| {});
        });
    });
}

fn scope_helper<'s, 'e>(s: &'s Scope<'s, 'e>) { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
    s.spawn(|| {});
}

pub fn via_scope_helper() { //~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::thread::scope::<
    std::thread::scope(|s| scope_helper(s)); //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
}

fn builder_helper<'s, 'e>(s: &'s Scope<'s, 'e>) { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _ = Builder::new().spawn_scoped(s, || 1u8);
}

pub fn via_builder_helper() { //~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::thread::scope::<
    std::thread::scope(|s| builder_helper(s)); //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
}

pub fn path_call() { //~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::thread::scope::<
    std::thread::scope(|s| { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
        Scope::spawn(s, || {});
    });
}
