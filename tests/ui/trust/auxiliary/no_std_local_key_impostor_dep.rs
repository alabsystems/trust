//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A `#![no_std]` dependency, compiled with verification OFF the way Targo
//! compiles every dependency unit, that CLAIMS std's `LocalKey` diagnostic item
//! for a struct of its own and ships a `thread_local!`-shaped constant key.
//!
//! In a graph that never loads std, nothing contests the claim: rustc rejects a
//! duplicate diagnostic item only when both owners are loaded. Its `try_with` has
//! the shape the const-init TLS lane's drift pin admits (no `Assert`, no local
//! callee, no `!`-returning callee, exactly one call through a `fn` pointer),
//! and it calls `boom` first, which panics on every call. The caller fixture
//! (`tls_try_with_local_key_diagnostic_item_impostor_refuted.rs`) proves that
//! call is not erased as total.
#![no_std]
#![feature(rustc_attrs, thread_local)]
#![allow(internal_features)]

#[derive(Debug, Clone, Copy)]
pub struct AccessError;

#[rustc_diagnostic_item = "LocalKey"]
pub struct LocalKey<T: 'static> {
    inner: fn(Option<&mut Option<T>>) -> *const T,
}

impl<T: 'static> LocalKey<T> {
    pub const unsafe fn new(inner: fn(Option<&mut Option<T>>) -> *const T) -> LocalKey<T> {
        LocalKey { inner }
    }

    pub fn try_with<F, R>(&'static self, f: F) -> Result<R, AccessError>
    where
        F: FnOnce(&T) -> R,
    {
        boom();
        let thread_local = unsafe { (self.inner)(None).as_ref().ok_or(AccessError)? };
        Ok(f(thread_local))
    }
}

#[inline(never)]
pub fn boom() {
    panic!("impostor LocalKey::try_with")
}

#[thread_local]
static VAL: u32 = 5;

// The accessor reads a `#[thread_local]` static and does nothing else, as the
// const-init accessor `thread_local!` expands to does.
pub const KEY: LocalKey<u32> = unsafe { LocalKey::new(|_| &raw const VAL) };
