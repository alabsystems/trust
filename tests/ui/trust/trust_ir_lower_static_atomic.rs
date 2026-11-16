//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-SI): a local static with INTERIOR mutability (`AtomicUsize`,
//! `AtomicBool`) is the mutable module global wave-SM gives a `static mut`:
//! its address is the `GlobalAddr`, every mutation is a call to the type's
//! own method with that address, and a read through it is a `Load` nothing
//! SSA-folds. Every body here carried `StaticRef(interior mutable)` before
//! the wave; `strict` turns that into a compile error, so this file is the
//! mutation check.
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
static HITS: AtomicUsize = AtomicUsize::new(0);
static DONE: AtomicBool = AtomicBool::new(false);
fn hit() -> usize {
    HITS.fetch_add(1, Ordering::Relaxed);
    HITS.load(Ordering::Relaxed)
}
fn finish() {
    DONE.store(true, Ordering::SeqCst);
}
fn done() -> bool {
    DONE.load(Ordering::SeqCst)
}
fn main() {
    let a = hit();
    let b = hit();
    finish();
    std::process::exit(!(a == 1 && b == 2 && done()) as i32);
}
