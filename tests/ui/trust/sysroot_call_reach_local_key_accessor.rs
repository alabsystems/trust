//@ revisions: handed_with handed_with_certify handed_try_with handed_set handed_replace
//@ revisions: handed_get handed_take handed_with_borrow
//@ revisions: dep_const_with dep_const_set dep_const_get
//@ revisions: local_const_with local_const_try_with local_const_get local_const_set
//@ revisions: std_key_panicking
//@ revisions: dep_const_try_with dep_const_replace dep_ok_with dep_ok_set
//@ revisions: handed_in_closure handed_method static_key_ref
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: sysroot_call_reach_local_key_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[handed_with_certify] compile-flags: -Ztrust-policy=certify
//@[handed_with] check-fail
//@[handed_with_certify] check-fail
//@[handed_try_with] check-fail
//@[handed_set] check-fail
//@[handed_replace] check-fail
//@[handed_get] check-fail
//@[handed_take] check-fail
//@[handed_with_borrow] check-fail
//@[dep_const_with] check-fail
//@[dep_const_set] check-fail
//@[dep_const_get] check-fail
//@[local_const_with] check-fail
//@[local_const_try_with] check-fail
//@[local_const_get] check-fail
//@[local_const_set] check-fail
//@[std_key_panicking] check-pass
//@[dep_const_try_with] check-fail
//@[dep_const_replace] check-fail
//@[dep_ok_with] check-fail
//@[dep_ok_set] check-fail
//@[handed_in_closure] check-fail
//@[handed_method] check-fail
//@[static_key_ref] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! CALL-REACH-1-D8 (docs/DECISION_QUEUE.md; KNOWN_HAZARDS, the D6 entry's
//! `LocalKey` bullet): a `thread_local!` key is a VALUE whose `inner` field is the
//! accessor `LocalKey::try_with` and `initialize_with` call as `(self.inner)(..)`.
//! The accessor of a lazily initialized key runs the key's initializer, which a
//! dependency may write to panic (`auxiliary/sysroot_call_reach_local_key_dep.rs`).
//!
//! BEFORE (stage 1 of main `3ed8b09dad`, measured 2026-10-13):
//!  * `handed_with`, `handed_try_with`, `handed_set`, `handed_replace`: a method
//!    called on a `&'static LocalKey<_>` the verified function was HANDED built
//!    exit 0 under the default policy with one runtime-checked row (certify
//!    refused). The call walk followed `try_with`'s accessor call only at a key it
//!    traced to a constant (R16 front A) and otherwise took D2's leaf, so it
//!    answered `closed(walk)`.
//!  * `dep_const_with`: `dep::BOMB.with(..)`, a key traced to a dependency's
//!    constant, opened the walk (it reaches `dep::BOMB::{constant#0}::{closure#1}`),
//!    yet built exit 0 under the default policy too: `with` and `try_with` are
//!    BUNDLED members, the bridge's deny arm claims only an absent callee, and
//!    `try_with`'s indirect call lowered to a havoc row the default policy reported
//!    as runtime-checked.
//!  * `dep_const_set`: `dep::BOMB.set(3)` built exit 0 under the default policy:
//!    `initialize_with`'s `(self.inner)(Some(..))` was D2's leaf even at a constant
//!    key (only `try_with`'s accessor call was followed).
//!  * `handed_get`, `handed_take`, `handed_with_borrow`, `dep_const_get`: already
//!    refused (a fail-closed absent-callee row); pinned so they stay refused.
//!
//! AFTER (D8): in a `LocalKey` method, a call through `(*self).inner` is followed to
//! the accessor read out of a CONSTANT key and otherwise OPENS the walk (an untraced
//! key, or a constant whose accessor does not read back); a `LocalKey` method call
//! is always walked (the pre-filter's type rule cannot see the key); and a call the
//! walk left open keeps its caller fail-closed under the default policy whichever
//! bridge arm lowered it. Every `handed_*` and `dep_*` revision is refused.
//!
//! PINNED AS-IS (each verdict and error set is the BEFORE one): a LOCAL
//! `thread_local!` constant key (`local_const_*`) — the file fails on the
//! expansion's other accessor (`K::{constant#0}::{closure#0}`), as
//! `tls_try_with_resident_std_local_key_keeps_credit.rs` records, `f` is reported
//! rather than refused for `with`/`try_with`/`set`, and refused for `get` (a generic
//! absent callee, as before); and std's own constant key behind
//! `std::thread::panicking()` (`std_key_panicking`), which the walk traces and
//! follows, stays accepted.
//!
//! ADDED BY REVIEW (2026-10-14), each built exit 0 under the default policy on main
//! `3ed8b09dad` and is refused by D8: `dep_const_try_with` and `dep_const_replace`
//! (the dependency key through `try_with`'s pinned R16 arm and through
//! `replace`/`initialize_with`), `handed_in_closure` (the gate's root is the closure),
//! `handed_method` (an inherent method reading the key out of `self`),
//! `static_key_ref` (a key read out of a `static`, untraced). `dep_ok_with` and
//! `dep_ok_set` pin D8's CAPABILITY COST: a dependency's key with a `const { .. }`
//! initializer cannot panic, yet its accessor is dependency code the walk cannot
//! close, so it is refused (main accepted it only through defect 2).

#![allow(dead_code)]

extern crate sysroot_call_reach_local_key_dep as dep;

use std::cell::{Cell, RefCell};
use std::thread::LocalKey;

#[cfg(handed_with)]
pub fn f(k: &'static LocalKey<Cell<u32>>) -> u32 {
    //[handed_with]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    k.with(|c| c.get())
}

#[cfg(handed_with_certify)]
pub fn f(k: &'static LocalKey<Cell<u32>>) -> u32 {
    k.with(|c| c.get())
}

#[cfg(handed_try_with)]
pub fn f(k: &'static LocalKey<Cell<u32>>) -> u32 {
    //[handed_try_with]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    match k.try_with(|c| c.get()) {
        Ok(v) => v,
        Err(_) => 0,
    }
}

#[cfg(handed_set)]
pub fn f(k: &'static LocalKey<Cell<u32>>) {
    //[handed_set]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    k.set(3)
}

#[cfg(handed_replace)]
pub fn f(k: &'static LocalKey<Cell<u32>>) -> u32 {
    //[handed_replace]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    k.replace(4)
}

#[cfg(handed_get)]
pub fn f(k: &'static LocalKey<Cell<u32>>) -> u32 {
    //[handed_get]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    k.get()
}

#[cfg(handed_take)]
pub fn f(k: &'static LocalKey<Cell<u32>>) -> u32 {
    //[handed_take]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    k.take()
}

#[cfg(handed_with_borrow)]
pub fn f(k: &'static LocalKey<RefCell<u32>>) -> u32 {
    //[handed_with_borrow]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    k.with_borrow(|v| *v)
}

#[cfg(dep_const_with)]
pub fn f() -> u32 {
    //[dep_const_with]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    dep::BOMB.with(|c| c.get())
}

#[cfg(dep_const_set)]
pub fn f() {
    //[dep_const_set]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    dep::BOMB.set(3)
}

#[cfg(dep_const_get)]
pub fn f() -> u32 {
    //[dep_const_get]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    dep::BOMB.get()
}

#[cfg(any(local_const_with, local_const_try_with, local_const_get, local_const_set))]
thread_local! {
    //[local_const_with,local_const_try_with,local_const_get,local_const_set]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::K::{constant#0}::{closure#0}`
    static K: Cell<u32> = const { Cell::new(5) };
}

#[cfg(local_const_with)]
pub fn f() -> u32 {
    K.with(|c| c.get())
}

#[cfg(local_const_try_with)]
pub fn f() -> u32 {
    match K.try_with(|c| c.get()) {
        Ok(v) => v,
        Err(_) => 0,
    }
}

#[cfg(local_const_get)]
pub fn f() -> u32 {
    //[local_const_get]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    K.get()
}

#[cfg(local_const_set)]
pub fn f() {
    K.set(3)
}

#[cfg(std_key_panicking)]
pub fn f() -> bool {
    std::thread::panicking()
}

#[cfg(dep_const_try_with)]
pub fn f() -> u32 {
    //[dep_const_try_with]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    match dep::BOMB.try_with(|c| c.get()) {
        Ok(v) => v,
        Err(_) => 0,
    }
}

#[cfg(dep_const_replace)]
pub fn f() -> u32 {
    //[dep_const_replace]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    dep::BOMB.replace(1)
}

#[cfg(dep_ok_with)]
pub fn f() -> u32 {
    //[dep_ok_with]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    dep::OK.with(|c| c.get())
}

#[cfg(dep_ok_set)]
pub fn f() {
    //[dep_ok_set]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    dep::OK.set(2)
}

#[cfg(handed_in_closure)]
pub fn f(k: &'static LocalKey<Cell<u32>>) -> u32 {
    let g = move || k.with(|c| c.get());
    //[handed_in_closure]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f::{closure#0}`
    g()
}

#[cfg(handed_method)]
pub struct S {
    pub k: &'static LocalKey<Cell<u32>>,
}

#[cfg(handed_method)]
impl S {
    pub fn f(&self) -> u32 {
        //[handed_method]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::S::f`
        self.k.with(|c| c.get())
    }
}

#[cfg(static_key_ref)]
static KEY: &LocalKey<Cell<u32>> = &dep::BOMB;

#[cfg(static_key_ref)]
pub fn f() -> u32 {
    //[static_key_ref]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_key_accessor::f`
    KEY.with(|c| c.get())
}
