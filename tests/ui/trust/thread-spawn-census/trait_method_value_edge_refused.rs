//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (W11 round 3): a TRAIT METHOD named as a value on a concrete
//! type. The fn item's type is `FnDef(<trait method>, [S])`, whose `DefId` is
//! the trait's declaration — bodyless, or external for `Default::default` /
//! `Clone::clone` — so the census pushed no edge to the local impl method that
//! spawns, and NO body was refused: `let f: fn(&S) = <S as Go>::go`,
//! `.map(<S as Go>::go)`, `.map(S::go)`, a `const` holding it, a promoted
//! holding it, `let f: fn() -> D = Default::default` and
//! `.map(Clone::clone)` (review probe n5.rs, 2026-09-29). A named trait method
//! is now resolved (`Instance::try_resolve` in the naming body's typing
//! environment) to the impl method it selects. W11 refused every naming body
//! as an UNKNOWN. Since P2 (design 2026-09-29-spawn-census-by-construction)
//! the census walks instances: a reification is an ESCAPES row (a CREATE), a
//! `const` or promoted holding one an ESCAPES row (a READ), the call through
//! the fn pointer INDIRECT, and a method handed to std code that calls it
//! (`Option::map`, `Iterator::map`, `FnOnce::call_once`) an S2 SPAWNS row.
//! `quiet` is the same shapes with a spawn-free `launch`: no row.

#![allow(dead_code)]
#![feature(fn_traits)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

trait Go {
    fn go(&self);
}
pub struct S;
impl Go for S {
    fn go(&self) { launch() } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
}

pub fn reify() { let f: fn(&S) = <S as Go>::go; f(&S) } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
//[spawning]~^ NOTE may spawn (indirect): an indirect call

pub fn map_qualified() { let _ = Some(&S).map(<S as Go>::go); } //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::option::Option::<&S>::map

pub fn map_short() { let _ = Some(&S).map(S::go); } //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::option::Option::<&S>::map

const TG: fn(&S) = <S as Go>::go;
pub fn in_const() { TG(&S) } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

pub fn in_promoted() { let f: &'static fn(&S) = &(<S as Go>::go as fn(&S)); f(&S) } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
//[spawning]~^ NOTE may spawn (indirect): an indirect call

pub fn call_once_trait_method() { std::ops::FnOnce::call_once(<S as Go>::go, (&S,)) } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled

// A local impl of a STD trait: the named item is `core`'s declaration.
pub struct D;
impl Default for D {
    fn default() -> D { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        launch();
        D
    }
}
pub fn default_as_fn_ptr() { let f: fn() -> D = Default::default; let _ = f(); } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
//[spawning]~^ NOTE may spawn (indirect): an indirect call

pub struct C;
impl Clone for C {
    fn clone(&self) -> C { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        launch();
        C
    }
}
pub fn clone_as_value(v: &[C]) -> Vec<C> { v.iter().map(Clone::clone).collect() } //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via <std::iter::Map<std::slice::Iter<'_, C>
