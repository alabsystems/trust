//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! W11 spawn census: a caller invoking a local spawning closure (or a local
//! spawning fn item) through a callable trait. `f()` on a closure of matching
//! kind resolves to the closure itself and already had an edge, but its row was
//! invisible in the text report: TrustIr lowering of the caller fails ("closure
//! body is not present in the TrustIr module") and the lowering-failure reason
//! replaced the row's own, so it read as failing closed by accident. The reason
//! now names the refusal. `FnOnce::call_once` on an `Fn` closure or on a fn item
//! resolves to a std shim (`ClosureOnceShim` / `FnPtrShim`), so resolution named
//! no local item at all: the fn-item caller carried NO spawn row, and the
//! closure caller only the body-level fallback. The census now reads the closure
//! / fn item off the call's self type and refuses the caller at the call.
//! `quiet` is the same shape with a spawn-free `launch`: no spawn row may appear.

#![allow(dead_code)]
#![feature(fn_traits)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub fn fn_closure() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    let f = || launch(); //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    f();
}

pub fn fnmut_closure() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    let mut calls = 0u8;
    let mut f = || { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        calls += 1;
        launch();
    };
    f();
}

pub fn fnonce_closure() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    let owned = vec![1u8];
    let f = move || { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        drop(owned);
        launch();
    };
    f();
}

pub fn call_once_shim() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    let f = || launch(); //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    std::ops::FnOnce::call_once(f, ());
}

pub fn fn_item_through_trait() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    std::ops::FnOnce::call_once(launch, ());
}

pub fn by_ref_call() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    let f = || launch(); //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    (&f)();
}
