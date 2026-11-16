//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census: a still-generic local fn NAMED as a value (reified to a fn
//! pointer, returned, stored in a const or static, handed to a generic
//! callee). Naming `make_drop::<Spawner>` as a value carried no row at all
//! before W11 (review probe t4.rs: `b_value`, `c_ret`, `d_const`, `d2_static`,
//! `g_thunk`), although whoever calls the value runs the same body; W11
//! refused the naming site as an UNKNOWN. Since P2 (design
//! 2026-09-29-spawn-census-by-construction) the census walks the instance
//! `make_drop::<Spawner>`, which drops a `Spawner` (S3): reifying it is an
//! ESCAPES row (a CREATE), reading it from a `const`/`static` is an ESCAPES
//! row (a READ), their callers are ESCAPES, and `repeat_with(..)` hands it to
//! std code that calls it exactly (S2). Every `fn()` call in the crate is
//! INDIRECT, because the `fn()` pool holds `make_drop::<Spawner>`
//! (`quiet_value`; design §7). `quiet` is the same shapes with a spawn-free
//! `Drop` impl.

#![allow(dead_code)]

#[cfg(spawning)]
pub fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    std::thread::spawn(|| {});
}
#[cfg(quiet)]
pub fn launch() {}

#[derive(Default)]
pub struct Spawner;
impl Drop for Spawner {
    fn drop(&mut self) { launch() } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
}

pub fn make_drop<T: Default>() { let _t = T::default(); } //[spawning]~ NOTE value dropped here has drop glue that may run a local Drop impl

pub fn b_value() { let f: fn() = make_drop::<Spawner>; f() } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
pub fn b_caller() { b_value() } //[spawning]~ NOTE callee names, erases or reads a callable that reaches a std thread spawn
pub fn c_ret() -> fn() { make_drop::<Spawner> } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
pub fn c_user() { c_ret()() } //[spawning]~ NOTE callee names, erases or reads a callable that reaches a std thread spawn
pub const MD: fn() = make_drop::<Spawner>;
pub fn d_const() { MD() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub static MDS: fn() = make_drop::<Spawner>;
pub fn d2_static() { MDS() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub fn g_thunk() { std::iter::repeat_with(make_drop::<Spawner>).take(1).for_each(drop) } //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops

// A drop-free type argument: reifying `make_drop::<u8>` is no row, but the
// call through the `fn()` pointer is INDIRECT (its pool holds
// `make_drop::<Spawner>`).
pub fn quiet_value() { let f: fn() = make_drop::<u8>; f() } //[spawning]~ NOTE may spawn (indirect): an indirect call
