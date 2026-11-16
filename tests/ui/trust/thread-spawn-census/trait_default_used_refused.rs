//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (W11 round 4): the control for
//! `trait_default_overridden_not_refused.rs`. A spawning trait default that is
//! USED (the impl does not override it: resolution selects the declaration
//! itself) is refused. Since P2 (design 2026-09-29-spawn-census-by-construction)
//! the resolved call `S.go()` and a call of an instance that resolves to the
//! default (`generic_call::<S>`) are S2 SPAWNS rows; the const read is an
//! ESCAPES row (a READ of the default's value), the reified method an ESCAPES
//! row (a CREATE), and every call through a fn pointer of shape `fn()` or
//! `fn(&S)` is INDIRECT (their pools hold `launch` and `S::go`), the
//! still-generic `generic_read` included. W11 refused all but `S.go()` as
//! UNKNOWNS. `generic_call` is SPAWNS through its instance `generic_call::<S>`
//! (the verdict joins over a definition's instances, design §5.3): R1 (DECISION_QUEUE
//! SC-3) leaves unrefused only a definition with no in-crate instance that spawns.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

trait Tr {
    const F: fn() = launch;
}
trait Go {
    fn go(&self) { launch() } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
}

pub struct S;
impl Tr for S {}
impl Go for S {}

pub fn const_default_used() { <S as Tr>::F() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub fn method_default_used_value() { let f: fn(&S) = <S as Go>::go; f(&S) } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
//[spawning]~^ NOTE may spawn (indirect): an indirect call
pub fn method_default_used_call() { S.go() } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
fn generic_read<T: Tr>() { T::F() } //[spawning]~ NOTE may spawn (indirect): an indirect call
fn generic_call<T: Go>(t: &T) { t.go() } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via <S as Go>::go
pub fn generic_call_user() { generic_call(&S) } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via generic_call::<S>
