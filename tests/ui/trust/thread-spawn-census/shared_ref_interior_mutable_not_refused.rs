//@ revisions: shared control
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[shared] forbid-output: through calls and drops
//@[shared] forbid-output: value dropped here
//@[shared] forbid-output: callable made into a fn pointer
//@[shared] forbid-output: const or static read here
//@[shared] forbid-output: callee names, erases or reads
//@[shared] forbid-output: value handed here to code
//@[shared] forbid-output: not enumerated (no spawn was found)
//! Spawn census: a SHARED reference to a value of an interior-mutable
//! (`!Freeze`) local type cannot run that type's own `Drop`. Through `&`, only
//! what an `UnsafeCell` holds can be replaced, and so dropped.
//!
//! Review of 638784cafa (2026-09-29, probes blk1_shared_cell.rs,
//! f1_shared_nonfreeze.rs, f2_arc_erase.rs): the drop-glue walk switched a whole
//! `!Freeze` type reached through `&` to "reachable", so it targeted the local
//! ADT's OWN `Drop`. `peek(&S)` (`size_of_val`) was refused as "value handed to
//! a callee that may drop it ... transitively spawns", and so were `ptr::eq`,
//! `format!("{:p}")`, `format!("{:?}")`, `Arc::clone(&arc)` and a `&dyn Debug`
//! erasure of a `Mutex`- or atomic-holding type, with every caller told its
//! callee "transitively spawns". None of these can spawn: none of the values
//! is ever dropped. W11's walk then stayed shared through every ADT, field by
//! field; only an `UnsafeCell` (directly, or as a field at any depth:
//! `Cell<T>`, `Mutex<T>`, `RefCell<T>` hold one, `Option<T>` and `Arc<T>` do
//! not) makes what it holds reachable.
//!
//! Review of b20206189c (2026-09-29, probes n3/n4/n7/n8): an EXTERNAL ADT was
//! judged interior-mutable by `Freeze` of the ADT with every type argument
//! replaced by `()`. A field that projects through a type argument
//! (`Peekable<I>` holds `Option<Option<I::Item>>`, `Flatten`/`FlatMap` hold
//! `<I::Item as IntoIterator>::IntoIter`) cannot normalize at `()`, so
//! `Peekable<()>` read as `!Freeze` and `p.size_hint()`, `format!("{:?}", p)`,
//! `size_of_val(p)`, `Option<Peekable<..>>::is_some`, `Flatten::size_hint` and a
//! `&dyn Debug` erasure on `&Peekable<vec::IntoIter<Job>>` were refused as
//! spawning (every caller told "transitively spawns", strict build errors
//! under default flags) though no `Job` is ever dropped. W11 then walked an
//! external ADT STRUCTURALLY too: its field types instantiated and normalized in
//! the body's typing environment, a raw pointer inside it or a fn pointer
//! field's output (its own ownership: `Box`, `Vec`'s buffer, `Arc`'s
//! `ArcInner`, `LocalKey`'s accessor) followed as shared, and a
//! `PhantomData<T>` read as a shared `T` (a `PhantomData<fn() -> U>` is a
//! variance marker: its fn pointer's output is not walked).
//!
//! W11 walked a raw pointer the body derives from a shared reference
//! (`ptr::eq(a, &LOG)` passes `&raw const (*a)`) as shared too, and one
//! derived from `&mut` as reachable.
//!
//! Since P2 (design 2026-09-29-spawn-census-by-construction) the census walks
//! every callee's instance, so what an API does behind `&` is visible, not
//! guessed from its types.
//!
//! `shared`: no body below the `Drop` impls drops a value with a spawning
//! `Drop`, so none carries a SPAWNS, ESCAPES or UNKNOWN row; the `Drop` impls'
//! direct spawns are the only claims. The formatting bodies (`addr`,
//! `dbg_len`, `peek_show` and their callers) are INDIRECT: `fmt::Arguments`
//! holds each argument as `NonNull<()>`, which carries any callable, so the
//! hand-off to `format` is charged with every pool, and the `dyn Debug` drop
//! pool holds `Stats`'s and `Peekable<IntoIter<Job>>`'s drop glue (the drop
//! slots of `as_dbg`'s and `peek_erase`'s vtables join it, design §5.4). That
//! is the design's precision cost (§7), not a claim.
//!
//! `control`: what an `UnsafeCell` holds is reachable through `&`, and the
//! census sees which APIs drop it: `Cell::set` drops the `Job` it replaces and
//! `LocalKey::with_borrow_mut(Vec::clear)` every `Job` in the thread-local (S2
//! SPAWNS rows); `Cell::take` is ESCAPES (std's optimized `take` no longer
//! shows a drop its stored mentions list, covered by an edge that claims
//! nothing). Size queries, `&` erasures, `Mutex::lock`, `ptr::eq`, `Weak`
//! counts, `OnceCell::get`, `MutexGuard` derefs and `Sender::clone` drop
//! nothing they hold and carry no row (W11 refused each as an UNKNOWN through
//! its `UnsafeCell`), and `LazyLock` deref is INDIRECT (its initializer is
//! called through a fn pointer).

#![allow(dead_code)]

use std::cell::Cell;
use std::fmt::Debug;
use std::iter::{FlatMap, Flatten, Peekable};
use std::sync::atomic::AtomicUsize;
use std::sync::{Arc, Mutex};

// blk1: a local `!Freeze` type (a `Cell<u8>` field) with a spawning `Drop`.
pub struct S {
    c: Cell<u8>,
}
impl Drop for S {
    fn drop(&mut self) { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
        let _h = std::thread::spawn(|| {});
    }
}

pub fn peek(s: &S) -> usize {
    std::mem::size_of_val(s)
}
pub fn caller(s: &S) -> usize {
    peek(s)
}
pub fn get(s: &S) -> u8 {
    s.c.get()
}
pub fn peek_opt(o: &Option<S>) -> usize {
    std::mem::size_of_val(o)
}

// f1: a `Mutex`-holding type that only ever lives in a `static`.
pub struct Logger {
    m: Mutex<Vec<u8>>,
}
impl Drop for Logger {
    fn drop(&mut self) { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
        let _h = std::thread::spawn(|| {});
    }
}
pub static LOG: Logger = Logger { m: Mutex::new(Vec::new()) };

// `ptr::eq` takes raw pointers: `&raw const (*a)` has shared-reference
// provenance, so it is walked as shared too.
pub fn same(a: &Logger) -> bool {
    std::ptr::eq(a, &LOG)
}
pub fn size(a: &Logger) -> usize {
    std::mem::size_of_val(a)
}
pub fn addr(a: &Logger) -> usize { //~ NOTE may spawn (indirect): an indirect call
    format!("{:p}", a).len()
}
pub fn log_len() -> usize {
    LOG.m.lock().map(|v| v.len()).unwrap_or(0)
}

// f2: an atomic-holding type shared through `Arc` and erased by `&`.
#[derive(Debug)]
pub struct Stats {
    n: AtomicUsize,
}
impl Drop for Stats {
    fn drop(&mut self) { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
        let _h = std::thread::spawn(|| {});
    }
}

pub fn share(a: &Arc<Stats>) -> Arc<Stats> {
    Arc::clone(a)
}
pub fn dbg_len(s: &Stats) -> usize { //~ NOTE may spawn (indirect): an indirect call
    format!("{:?}", s).len()
}
pub fn as_dbg(s: &Stats) -> &dyn Debug {
    s
}
pub fn users(s: &Stats, a: &Arc<Stats>) -> usize {
    dbg_len(s) + Arc::strong_count(a) + std::mem::size_of_val(as_dbg(s))
}

// n3/n4/n7/n8: external wrappers whose fields project through a type argument.
// No `Job` is ever dropped, and none of these can drop one.
#[derive(Debug)]
pub struct Job(u8);
impl Drop for Job {
    fn drop(&mut self) { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
        let _h = std::thread::spawn(|| {});
    }
}

pub fn peek_hint(p: &Peekable<std::vec::IntoIter<Job>>) -> (usize, Option<usize>) {
    p.size_hint()
}
pub fn peek_show(p: &Peekable<std::vec::IntoIter<Job>>) -> String { //~ NOTE may spawn (indirect): an indirect call
    format!("{:?}", p)
}
pub fn peek_size(p: &Peekable<std::vec::IntoIter<Job>>) -> usize {
    std::mem::size_of_val(p)
}
pub fn peek_caller(p: &Peekable<std::vec::IntoIter<Job>>) -> usize {
    peek_hint(p).0 + peek_size(p)
}
pub fn peek_in_option(p: &Option<Peekable<std::option::IntoIter<Job>>>) -> bool {
    p.is_some()
}
pub fn flat_hint(f: &Flatten<std::vec::IntoIter<Vec<Job>>>) -> (usize, Option<usize>) {
    f.size_hint()
}
pub fn flat_map_hint(
    f: &FlatMap<std::vec::IntoIter<u8>, Vec<Job>, fn(u8) -> Vec<Job>>,
) -> (usize, Option<usize>) {
    f.size_hint()
}
pub fn peek_erase(p: &Peekable<std::vec::IntoIter<Job>>) -> &dyn Debug {
    p
}
// blk1 inside the wrapper: `S` holds a `Cell<u8>`, which holds nothing droppable.
pub fn peek_cell_elements(p: &Peekable<std::vec::IntoIter<S>>) -> usize {
    std::mem::size_of_val(p)
}
pub fn wrapper_users(p: &Peekable<std::vec::IntoIter<Job>>) -> usize {
    peek_caller(p) + peek_show(p).len() + std::mem::size_of_val(peek_erase(p))
}

// Review probe q3 `pf_ref`: a `PhantomData<fn() -> ..>` is a variance marker
// whose fn pointer is never called, so its output is not walked. Walking it
// recursed through `Pf<(T, T)>` until the budget ran out, and the `Wrap`
// projection field made the fallback opaque: an unknown on a spawn-free body.
pub struct Wrap<I: Iterator> {
    cur: Option<I::Item>,
    it: I,
}
pub struct Pf<T> {
    v: T,
    p: std::marker::PhantomData<fn() -> Pf<(T, T)>>,
    w: std::marker::PhantomData<Wrap<std::vec::IntoIter<T>>>,
}
pub fn pf_ref(p: &Pf<String>) {
    let _ = std::hint::black_box(p);
}

// control: the spawning value sits INSIDE an `UnsafeCell`, so `&` reaches it,
// and the census walks each API to see whether it drops it. Every row sits on
// its function's first line (a function's rows are notes on that function's
// diagnostic). These drop nothing they reach: no row.
#[cfg(control)]
pub struct Holder {
    c: Cell<Option<S>>,
}

#[cfg(control)]
pub fn peek_holder(h: &Holder) -> usize {
    std::mem::size_of_val(h)
}

#[cfg(control)]
pub fn erase_holder(h: &'static Holder) -> &'static dyn std::any::Any {
    h
}

#[cfg(control)]
pub fn lock_logger(m: &Mutex<Logger>) -> bool {
    m.lock().is_ok()
}

// `ptr::eq` only compares the pointers: no row (W11 refused a raw pointer
// derived from `&mut` handed to any external callee).
#[cfg(control)]
pub fn hand_mut_raw(a: &mut Logger) -> bool {
    std::ptr::eq(a as *mut Logger, a as *mut Logger)
}

// An `UnsafeCell` reached through `&` really lets code drop what it holds:
// `set` drops the `Job` it replaces (S2 through `Cell::set`). `take` moves it
// out; std's optimized `take` lost a drop its stored mentions list, which is
// covered by an edge that claims nothing (ESCAPES).
#[cfg(control)]
pub fn cell_set(c: &Cell<Option<Job>>) { //[control]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::cell::Cell::<std::option::Option<Job>>::set
    c.set(None)
}

#[cfg(control)]
pub fn cell_take(c: &Cell<Option<Job>>) -> Option<Job> { //[control]~ NOTE callee names, erases or reads a callable that reaches a std thread spawn
    c.take()
}

// The same `UnsafeCell` inside an external wrapper's elements: a size query
// drops nothing.
#[cfg(control)]
pub fn peek_cell_holders(p: &Peekable<std::vec::IntoIter<Cell<Option<Job>>>>) -> usize {
    std::mem::size_of_val(p)
}

// Reached through an external ADT's own pointers: `Weak::strong_count` drops
// nothing, and `LocalKey::with_borrow_mut(Vec::clear)` drops every `Job` in the
// thread-local through the shared `&LocalKey` (S2).
#[cfg(control)]
pub fn weak_count(w: &std::sync::Weak<Mutex<Option<Job>>>) -> usize {
    w.strong_count()
}

#[cfg(control)]
pub fn tls_key_clear(k: &'static std::thread::LocalKey<std::cell::RefCell<Vec<Job>>>) { //[control]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::thread::LocalKey::
    k.with_borrow_mut(Vec::clear)
}

// W11's structural walk refused each of these as an UNKNOWN (an `UnsafeCell`
// anywhere inside was reachable). The census sees that none drops a `Job`;
// `LazyLock` deref calls its initializer through a fn pointer (INDIRECT).
#[cfg(control)]
pub fn lazy_get(l: &'static std::sync::LazyLock<Job>) -> u8 { //[control]~ NOTE may spawn (indirect): an indirect call
    l.0
}

#[cfg(control)]
pub fn once_get(c: &std::cell::OnceCell<Job>) -> bool {
    c.get().is_some()
}

#[cfg(control)]
pub fn guard_deref(g: &std::sync::MutexGuard<'_, Job>) -> u8 {
    g.0
}

#[cfg(control)]
pub fn sender_clone(t: &std::sync::mpsc::Sender<Job>) -> std::sync::mpsc::Sender<Job> {
    t.clone()
}
