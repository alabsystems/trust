//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census: a callable handed on as a VALUE. The body that finally
//! calls it is still-generic (`run_value`, whose `F::call_once` names no item)
//! or indirect (`run_ptr`, a fn-pointer call). Until W11 none of
//! `run_value(launch)`, `run_ptr(launch)`, a reified spawning closure and
//! `.map(std::thread::spawn)` carried a row; W11 refused the NAMING body as an
//! UNKNOWN. Since P2 (design 2026-09-29-spawn-census-by-construction, the
//! census walks instances): a callable handed to a generic callee that calls
//! it is S2 through that instance (`run_value::<fn() {launch}>`,
//! `Iterator::for_each`, `Option::map`), so those callers are SPAWNS rows; a
//! callable made into a fn pointer is an ESCAPES row where it is reified, and
//! the fn-pointer call in `run_ptr` is INDIRECT (its FnPool holds `launch`),
//! as is every caller of `run_ptr`. `quiet` is the same shape with a
//! spawn-free `launch` and `map` target: no spawn row may appear.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

fn run_value<F: FnOnce()>(f: F) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops
    f()
}

fn run_ptr(f: fn()) { //[spawning]~ NOTE may spawn (indirect): an indirect call
    f()
}

pub fn fn_item_to_generic() { run_value(launch); } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via run_value::<fn() {launch}> → launch

pub fn fn_item_reified() { run_ptr(launch); } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn
//[spawning]~^ NOTE may spawn (indirect): the callee, value or callable here reaches an indirect call

pub fn closure_reified() { let f: fn() = || launch(); run_ptr(f); } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn
//[spawning]~^ NOTE may spawn (indirect): the callee, value or callable here reaches an indirect call

fn launch_one(_: &u8) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    launch();
}

pub fn fn_item_for_each(v: &[u8]) { v.iter().for_each(launch_one); } //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via <std::slice::Iter<'_, u8> as std::iter::Iterator>::for_each

#[cfg(spawning)]
pub fn std_spawn_as_value() { let _ = Some(|| {}).map(std::thread::spawn); } //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::option::Option::

#[cfg(quiet)]
pub fn std_spawn_as_value() { let _ = Some(0u8).map(|x| x); }
