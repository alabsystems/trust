//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census: drop glue that runs a local `Drop::drop` which spawns.
//! A `Drop` terminator is not a call, so before W11 the census had no edge
//! from a body that drops such a value (directly, through a local ADT field,
//! or through a container's generic argument) and the body carried no
//! `UnmodeledThreadSpawnEffect` row. W11 refused a call HANDING the value to
//! a callee as an UNKNOWN ("may drop it"), whatever the callee did. Since P2
//! (design 2026-09-29-spawn-census-by-construction) the census walks the
//! callee's instance: `mem::drop::<Spawner>` and the local generic
//! `consume::<Spawner>` drop it (S3 inside them), so their callers are S2
//! SPAWNS rows; `m.lock()` on `&Mutex<Spawner>` and `mem::swap` drop no
//! `Spawner` (their bodies say so), so `lock` and `swap` carry no row. A
//! call that is handed nothing droppable is not a drop site
//! (`type_named_without_drop_not_refused.rs`). `quiet` is the same shape with
//! a spawn-free `Drop::drop`.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub struct Spawner;

impl Drop for Spawner {
    fn drop(&mut self) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        launch();
    }
}

pub struct Holder {
    inner: Option<Spawner>,
}

pub fn drops_local() { //[spawning]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    let _s = Spawner;
}

pub fn drops_field(_h: Holder) {} //[spawning]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled

pub fn drops_container(_v: Vec<Spawner>) {} //[spawning]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled

pub fn explicit_mem_drop(s: Spawner) { //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::mem::drop::<Spawner> → drop glue of `Spawner`
    std::mem::drop(s);
}

pub fn drop_caller() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    drops_local();
}

fn consume<T>(_value: T) {} //[spawning]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops

pub fn generic_consumer() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via consume::<Spawner> → drop glue of `Spawner`
    consume(Spawner);
}

// Handed to an external callee that does not drop it: the census walks
// `Mutex::lock` (the `MutexGuard` in the dropped `LockResult` holds only a
// `&Mutex`) and `mem::swap`, and neither drops a `Spawner`. W11 refused both
// (an UNKNOWN through `&`, a "may drop" hand-off through `&mut`).
pub fn lock(m: &std::sync::Mutex<Spawner>) -> bool { m.lock().is_ok() }

pub fn swap(a: &mut Spawner, b: &mut Spawner) { std::mem::swap(a, b) }
