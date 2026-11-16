//@ revisions: spawning quiet
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! W11 spawn census: the edges the census documents for coroutine-closures,
//! coroutines, closure upvars, thread-local statics, nested statics and a
//! `Box<dyn Fn()>`, each pinned where its row lands (review of 638784cafa,
//! 2026-09-29: the census refused all of these, but no test held them).
//!
//! * `AsyncFn*`: a call of a coroutine-closure is a callable-trait call whose
//!   self type is the closure; the edge is read off that self type. `c()` on a
//!   LENDING closure (its future borrows the closure's upvar, so it has only the
//!   `AsyncFn*` impls) and on an `impl AsyncFn()` returned by another fn (the
//!   closure is named only by that fn; the row at `c()` is the self-type edge).
//! * Coroutine drop glue: dropping a future (a MIR `Drop` of a coroutine) runs
//!   the drops of what it holds, a `Spawner` held across an `.await` or moved
//!   into an `async move` block.
//! * Closure-upvar drop glue: dropping a `move` closure drops its upvars.
//! * Thread-local statics: `thread_local!` (lazy and `const`-initialized) read
//!   through `LocalKey::with` (the macro's `LocalKey` const is the read), and a
//!   nightly `#[thread_local]` static, read as a `ThreadLocalRef`.
//! * A nested `static` named by another static's initializer (`&SHOOK`).
//! * `Box<dyn Fn()>`: `make_dyn_fn` (a fn item erased to `dyn Fn`) and
//!   `boxed_dyn_fn` (a closure) are refused where the callable is erased, and
//!   `call_dyn_fn`, which calls the trait object, where it is called.
//!
//! Since P2 (design 2026-09-29-spawn-census-by-construction) the census walks
//! instances and decomposes drop glue structurally. A coroutine-closure call
//! builds a future and runs none of its body, and a future that is never
//! polled runs none either, so `call_made_async` carries no row (W11: an
//! UNKNOWN); `lending_async_closure_called` is INDIRECT only because dropping
//! its `String` deallocates, and std's deallocation and panic paths call a
//! thread-local accessor through a fn pointer whose pool holds `TL_FN`'s
//! accessor, which mints `launch` (design §7, the cost of shape-keyed pools).
//! Dropping a future runs the drops of what its saved state may hold (a
//! `Spawner` across an `.await`, or moved into an `async move` block): an S3
//! SPAWNS row, as is a `move` closure's by-value upvar. A thread-local,
//! `static` or promoted read is an ESCAPES row (a READ), a fn item or closure
//! erased to `dyn Fn` an ESCAPES row (a CREATE), and the call through the
//! trait object INDIRECT where it happens (`call_dyn_fn`; W11 left it
//! unrefused). Nothing refused before is quiet except the future that is never
//! polled and the async-closure call.
//!
//! `quiet` is the same shapes with a spawn-free `launch`: no row at all (the
//! pattern has no space after the colon: compiletest keeps a directive's value
//! verbatim, and the kind is printed after a backtick).

#![allow(dead_code)]
#![feature(thread_local)]

use std::cell::Cell;

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub struct Spawner;

impl Drop for Spawner {
    fn drop(&mut self) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        launch()
    }
}

// Every row of a function is a note on that function's diagnostic, so the
// annotations sit on the function's first line: each names a row kind the
// body must carry.

// --- `AsyncFn*`: calling a local coroutine-closure --------------------------

pub fn lending_async_closure_called() {
    //[spawning]~^ NOTE may spawn (indirect): the callee, value or callable here reaches an indirect call
    let tag = String::new();
    let c = async || {
        let _t = &tag;
        launch()
    };
    let _fut = c();
}

fn make_async() -> impl AsyncFn() {
    async || launch()
}

// The future `c()` builds is dropped unpolled and holds nothing that drops a
// `Spawner`: no row.
pub fn call_made_async() {
    let c = make_async();
    let _fut = c();
}

// --- coroutine drop glue ----------------------------------------------------

pub async fn hold_spawner() {
    let _s = Spawner;
    std::future::ready(()).await;
}

pub fn drop_future_terminator() {
    //[spawning]~^ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled (via drop glue of `{async fn body of hold_spawner()}`
    let _f = hold_spawner();
}

pub fn drop_async_block(s: Spawner) {
    //[spawning]~^ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    let f = async move {
        let _t = &s;
        std::future::ready(()).await;
    };
    let _g = f;
}

// --- closure-upvar drop glue ------------------------------------------------

pub fn closure_upvar_drop(s: Spawner) {
    //[spawning]~^ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    let c = move || {
        let _t = &s;
    };
    c();
}

// --- thread-local statics ---------------------------------------------------

thread_local!(static TL_FN: Cell<fn()> = Cell::new(launch));

pub fn tl_read() {
    //[spawning]~^ NOTE const or static read here holds a callable that reaches a std thread spawn
    TL_FN.with(|c| (c.get())())
}

thread_local!(static TL_HOOK: fn() = launch);

pub fn tl_hook() {
    //[spawning]~^ NOTE const or static read here holds a callable that reaches a std thread spawn
    TL_HOOK.with(|h| h())
}

thread_local!(static TL_CONST: Cell<Option<fn()>> = const { Cell::new(Some(launch)) });

pub fn tl_const_read() {
    //[spawning]~^ NOTE const or static read here holds a callable that reaches a std thread spawn
    TL_CONST.with(|c| {
        if let Some(f) = c.get() {
            f()
        }
    })
}

#[thread_local]
static RAW_TL: Cell<fn()> = Cell::new(launch);

pub fn raw_tl_read() {
    //[spawning]~^ NOTE const or static read here holds a callable that reaches a std thread spawn
    (RAW_TL.get())()
}

// --- a nested static --------------------------------------------------------

pub static SHOOK: fn() = launch;
pub static OUTER: &fn() = &SHOOK;

pub fn nested_static() {
    //[spawning]~^ NOTE const or static read here holds a callable that reaches a std thread spawn
    (*OUTER)()
}

// --- `Box<dyn Fn()>` --------------------------------------------------------

pub fn make_dyn_fn() -> Box<dyn Fn()> {
    //[spawning]~^ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
    Box::new(launch)
}

pub fn boxed_dyn_fn() -> Box<dyn Fn()> {
    //[spawning]~^ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
    Box::new(|| launch())
}

pub fn call_dyn_fn(f: Box<dyn Fn()>) { //[spawning]~ NOTE may spawn (indirect): an indirect call
    f()
}

pub fn user_dyn_fn() {
    //[spawning]~^ NOTE callee names, erases or reads a callable that reaches a std thread spawn
    //[spawning]~| NOTE may spawn (indirect): the callee, value or callable here reaches an indirect call
    call_dyn_fn(make_dyn_fn())
}
