//@ needs-trust-verify
//@ build-pass
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN

//! **Regression: a `Drop` impl whose conversion callee drops the same type
//! must not become an E0391 query cycle.**
//!
//! MEASURED 2026-09-08 on `first-party/ty`'s vendored `rowan` (`arc.rs`):
//! `impl Drop for ThinArc { fn drop(&mut self) { let _ = Arc::from_thin(ThinArc { .. }) } }`
//! and `from_thin` forgets its argument AFTER a call that can unwind — so the
//! cleanup path DROPS a `ThinArc`. `drop`'s verification asked for
//! `from_thin`'s optimized MIR (a callee summary; the Call-only callgraph sees
//! no cycle), `from_thin`'s structural-drop lane then asked for `drop`'s proof
//! results while `drop`'s `optimized_MIR` was still on the query stack, and
//! rustc answered `error[E0391]: cycle detected when retrieving trust proof
//! results from MIR` — a hard error under EVERY policy, in a crate the user
//! does not own. The lane now consults the in-progress ancestor set before the
//! query and declines (the drop keeps its obligation). `build-pass` under
//! advisory is the assertion.

use std::marker::PhantomData;

struct Thin<T> {
    raw: *mut u8,
    phantom: PhantomData<T>,
}

struct Fat<T> {
    raw: *mut u8,
    phantom: PhantomData<T>,
}

impl<T> Drop for Thin<T> {
    fn drop(&mut self) {
        let _ = Fat::<T>::from_thin(Thin::<T> { raw: self.raw, phantom: PhantomData });
    }
}

impl<T> Fat<T> {
    fn from_thin(a: Thin<T>) -> Self {
        // `widen` can unwind, and `a` is only forgotten AFTER it — so the cleanup
        // path of this function drops a `Thin<T>`: the edge the Call graph never sees.
        let raw = widen(a.raw);
        std::mem::forget(a);
        Fat { raw, phantom: PhantomData }
    }
}

impl<T> Drop for Fat<T> {
    fn drop(&mut self) {
        if !self.raw.is_null() {
            unsafe { drop(Box::from_raw(self.raw)) }
        }
    }
}

#[inline(never)]
fn widen(p: *mut u8) -> *mut u8 {
    assert!(!p.is_null(), "a thin pointer is never null");
    p
}

fn main() {
    let t: Thin<u8> = Thin { raw: Box::into_raw(Box::new(7u8)), phantom: PhantomData };
    drop(t);
}
