//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census: a concrete value erased to `dyn Trait`. The call through the
//! trait object names no item, so the W11 round-1 census had no edge for
//! `make_dyn_go` (erasing a local type whose `Go::go` spawns) or `user`, nor
//! for an `Rc` whose drop glue spawns erased to `Rc<dyn Any>` (dyn.rs probe,
//! 2026-09-29: no body refused). W11 then refused the ERASING body as an
//! UNKNOWN and left the body that calls the object unrefused. Since P2 (design
//! 2026-09-29-spawn-census-by-construction §5.4) the erasure is an ESCAPES row
//! (the vtable's `go` slot and drop slot join the pools of `dyn Go` and
//! `dyn Any`), and the call through the object is refused where it is called:
//! `call_dyn_go`'s `g.go()` is INDIRECT (the `dyn Go` method pool holds
//! `GoSpawner::go`), and so is `user`, which also calls `make_dyn_go`
//! (ESCAPES). `Box::new(DropSpawner)` is S2: `Box::new` drops its argument on
//! its unwind path. `quiet` is the same shapes with spawn-free bodies: no
//! spawn row may appear.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub trait Go {
    fn go(&self);
}

pub struct GoSpawner;

impl Go for GoSpawner {
    fn go(&self) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        launch()
    }
}

pub fn make_dyn_go() -> Box<dyn Go> { Box::new(GoSpawner) } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called

pub fn ref_dyn_go(s: &GoSpawner) -> &dyn Go { s } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called

pub fn call_dyn_go(g: Box<dyn Go>) { g.go() } //[spawning]~ NOTE may spawn (indirect): an indirect call

pub fn user() { call_dyn_go(make_dyn_go()) } //[spawning]~ NOTE callee names, erases or reads a callable that reaches a std thread spawn
//[spawning]~^ NOTE may spawn (indirect): the callee, value or callable here reaches an indirect call

pub struct DropSpawner;

impl Drop for DropSpawner {
    fn drop(&mut self) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        launch()
    }
}

// The erasure's span is the `Box::new(..)` call's, whose S2 row is stronger;
// one row per position.
pub fn erase_any() -> Box<dyn std::any::Any> { Box::new(DropSpawner) } //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::boxed::Box::<DropSpawner>::new → drop glue of `DropSpawner`

pub fn erase_rc(r: std::rc::Rc<DropSpawner>) -> std::rc::Rc<dyn std::any::Any> { r } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called; the calls through it are not enumerated at this site; effect is unmodeled (fail-closed; not a spawn claim) (via drop glue of `DropSpawner`

// A SHARED reference to a `Freeze` value erased to `dyn`: dropping the pointee
// through it is undefined behavior, and `Any` has no local method: no row. (A
// `&mut` erasure IS a drop observation: `mut_dyn_erasure_drop_refused.rs`.)
pub fn erase_ref(s: &'static DropSpawner) -> &'static dyn std::any::Any { s }
