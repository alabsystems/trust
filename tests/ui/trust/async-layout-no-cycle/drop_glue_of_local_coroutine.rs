//@ revisions: off adv
//@ aux-build:coroutine_dropper.rs
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//@ forbid-output: internal compiler error
//! The drop glue of a LOCAL coroutine, reached through `ptr::drop_in_place`
//! (P2 review, probe dg1 and the drop-in sweep): `ManuallyDrop::drop`,
//! `MaybeUninit::assume_init_drop`, `Arc`/`Rc` of a future, an async closure's
//! future, a dependency's generic code, and a combinator that drops its future
//! in place (futures-util's `Map`). `drop_in_place` calls `core::ptr::drop_glue`,
//! and rustc's resolver answers that call for a coroutine by demanding the
//! coroutine's `optimized_mir` (to look for an async drop), whose
//! `inner_optimized_mir` forces the spawn census: the census asked the resolver
//! from inside its own provider, an E0391 on valid Rust in the verified lane
//! (`trustc`'s default) that `-Ztrust-verify=off` never showed. The census now
//! decomposes that drop glue itself, as for every drop (design §5.3, §8), so no
//! revision has a cycle, and the glue's spawn is still seen: `kill_spawner`'s
//! coroutine holds a `Guard` whose `Drop` spawns.
//!
//! Drop-in (release gate): stock rustc accepts this crate, and so does every
//! revision here.

#![allow(dead_code)]

extern crate coroutine_dropper;

use std::mem::{ManuallyDrop, MaybeUninit};

pub async fn yield_now() {}

pub async fn work() -> u8 {
    let s = String::from("x");
    yield_now().await;
    s.len() as u8
}

pub fn kill() {
    let mut f = ManuallyDrop::new(work());
    unsafe { std::ptr::drop_in_place(&mut *f as *mut _) }
}

pub fn drop_in_place_block() {
    let s = String::from("x");
    let mut f = async move { drop(s) };
    unsafe { std::ptr::drop_in_place(&mut f as *mut _) };
    std::mem::forget(f);
}

pub fn manually_drop() {
    let s = String::from("x");
    let mut fut = ManuallyDrop::new(async move {
        let t = s;
        std::future::ready(1).await;
        drop(t);
    });
    unsafe { ManuallyDrop::drop(&mut fut) };
}

pub fn maybe_uninit() {
    let s = String::from("x");
    let mut fut = MaybeUninit::new(async move {
        let _t = &s;
        std::future::ready(1).await;
    });
    unsafe { fut.assume_init_drop() };
}

pub fn arc() -> usize {
    let s = String::from("y");
    let a = std::sync::Arc::new(async move { s.len() });
    let b = a.clone();
    drop(a);
    std::sync::Arc::strong_count(&b)
}

pub fn rc() -> usize {
    let a = std::rc::Rc::new(work());
    std::rc::Rc::strong_count(&a)
}

pub fn async_closure() {
    let s = String::from("x");
    let f = async move || drop(s.clone());
    let mut m = ManuallyDrop::new(f());
    unsafe { ManuallyDrop::drop(&mut m) }
}

pub fn cross_crate() { coroutine_dropper::drop_it(work()) }

pub fn combinator() {
    let mut a = work();
    coroutine_dropper::replace_in_place(&mut a, work());
}

pub struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {
        let _handle = std::thread::spawn(|| {});
    }
}

pub async fn hold_guard() {
    let _g = Guard;
    yield_now().await;
}

pub fn kill_spawner() { //[adv]~ NOTE callee reaches a std thread spawn through calls and drops
    let mut f = ManuallyDrop::new(hold_guard());
    unsafe { std::ptr::drop_in_place(&mut *f as *mut _) }
}
