//@ run-pass
//@ revisions: o0 o1 o3
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@[o0] compile-flags: -Copt-level=0
//@[o1] compile-flags: -Copt-level=1
//@[o3] compile-flags: -Copt-level=3
//@ normalize-stderr: "\[[0-9a-f]{4}\]" -> "[HASH]"
//! Trust (F2, 2026-09-29): a user `impl Fn*` is a NON-closure `extern "rust-call"` body, so
//! rustc builds it with `spread_arg = Some(_2)` — codegen untuples the tuple argument into the
//! ABI's arguments by it. The flip's derived body is `Body::new`, `spread_arg: None`, and the
//! ABI gate compared only `arg_count` and the local types, so it installed the derived body:
//! `arg_local_refs` then read `_2` as an ordinary argument and indexed past `fn_abi.args`.
//! Measured on the pre-fix driver (fbb9fa383d): an ICE at `rustc_codegen_ssa/src/mir/mod.rs:505`
//! ("index out of bounds: the len is 1 but the index is 1") at `-Copt-level=0`, 1 and 3, on a
//! program stock rustc and `-Ztrust-ir-flip=no` compile and run. The gate now refuses a body
//! whose spread differs from built's, and the program runs.
//!
//! `check-pass` could not see this (tests/ui/trust/trust_ir_lower_rust_call_user_impl.rs has
//! the shape and never codegens); this test builds and RUNS.
//!
//! The GENERIC impl `G<T>` (review, 2026-09-29) reaches the INSTANCE lane instead: the DefId
//! seam refuses its generic signature, and `instance_flip::derive_instance_flip_body` used to
//! install the instantiated derived body with `spread_arg: None` — the same ICE (measured on the
//! tip driver at -O0/-O1 with `by_ref_generic`; `-Ztrust-instance-flip=no` built and printed 42).
//!
//! The expected stderr is EMPTY (no per-revision `.stderr` file). Since 51558bd9ff
//! (EXACT-THIR-ABI-1) the producer refuses every source `extern "rust-call"` body header
//! (`BodyHeader(unsupported source ABI or missing body)`: rust-call has no IR convention until a
//! real tuple adapter exists) and every caller of a rust-call method (`Callee(unsupported source
//! ABI)`), so neither flip lane derives a body here and none logs a fallback. Before, each
//! user impl body was derived and the flip refused it at WARN (`spread_arg mismatch: derived None
//! vs built Some(_2)`, and `shim: abi rederive: generic fn signature` for `G<T>`'s DefId seam).
//! The gate's spread rule keeps its unit control
//! (`flip_refinement_tests::the_spread_arg_refusal_refuses_every_mismatch_and_nothing_else`).
//! A body that is derived again either logs its fallback here, which changes the expected
//! stderr, or flips: a flip without the built spread is the ICE above, and this test RUNS.

#![feature(unboxed_closures, fn_traits)]

struct S;

impl Fn<()> for S {
    extern "rust-call" fn call(&self, _a: ()) -> i32 {
        42
    }
}
impl FnMut<()> for S {
    extern "rust-call" fn call_mut(&mut self, _a: ()) -> i32 {
        43
    }
}
impl FnOnce<()> for S {
    type Output = i32;
    extern "rust-call" fn call_once(self, _a: ()) -> i32 {
        44
    }
}

// A NON-EMPTY spread tuple, whose value the body ignores.
struct P;

impl Fn<(i32, bool)> for P {
    extern "rust-call" fn call(&self, _a: (i32, bool)) -> i32 {
        7
    }
}
impl FnMut<(i32, bool)> for P {
    extern "rust-call" fn call_mut(&mut self, _a: (i32, bool)) -> i32 {
        8
    }
}
impl FnOnce<(i32, bool)> for P {
    type Output = i32;
    extern "rust-call" fn call_once(self, _a: (i32, bool)) -> i32 {
        9
    }
}

// A GENERIC user impl: monomorphized, so it flips (if at all) on the instance lane.
struct G<T>(T);

impl<T> Fn<()> for G<T> {
    extern "rust-call" fn call(&self, _a: ()) -> i32 {
        42
    }
}
impl<T> FnMut<()> for G<T> {
    extern "rust-call" fn call_mut(&mut self, _a: ()) -> i32 {
        43
    }
}
impl<T> FnOnce<()> for G<T> {
    type Output = i32;
    extern "rust-call" fn call_once(self, _a: ()) -> i32 {
        44
    }
}

#[inline(never)]
fn by_ref_generic(s: &G<u8>) -> i32 {
    s()
}

#[inline(never)]
fn by_fn<F: Fn() -> i32>(f: F) -> i32 {
    f()
}

#[inline(never)]
fn by_fn_mut<F: FnMut() -> i32>(mut f: F) -> i32 {
    f()
}

#[inline(never)]
fn by_fn_once<F: FnOnce() -> i32>(f: F) -> i32 {
    f()
}

#[inline(never)]
fn by_ref(s: &S) -> i32 {
    s()
}

#[inline(never)]
fn with_args<F: Fn(i32, bool) -> i32>(f: F) -> i32 {
    f(1, true)
}

fn main() {
    assert_eq!(by_fn(S), 42);
    assert_eq!(by_fn_mut(S), 43);
    assert_eq!(by_fn_once(S), 44);
    assert_eq!(by_ref(&S), 42);
    assert_eq!(with_args(P), 7);
    assert_eq!(by_ref_generic(&G(1u8)), 42);
    assert_eq!(by_fn(G(2u16)), 42);
    assert_eq!(by_fn_mut(G('x')), 43);
    assert_eq!(by_fn_once(G(3i64)), 44);
}
