//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Trust (D8-P0, 2026-09-23): the CONTROL for
//! `assume_total_does_not_cover_unsafe.rs`. A `#[trust::assume_total]` body with
//! NO unsafe operation keeps its skip: `x + 1` may overflow, the attribute
//! assumes it does not, and the build passes exactly as before (measured rc=0,
//! zero warnings, on the stage-1 `trustc` of 2026-09-23). WARN annotations are
//! REQUIRED in this file on purpose: the "`assume_total` ... does not cover its
//! unsafe operations" warning appearing here would fail the test, so a
//! carve-out that stopped distinguishing safe bodies from unsafe ones is caught.
//! (`-O0` only: at `-O2` `total` is inlined into `caller`, whose own overflow
//! row refuses the crate today for a reason unrelated to this carve-out.)
//!
//! A `format_args!` desugaring wraps `Arguments::new` in a COMPILER-GENERATED
//! unsafe block; `print_total` pins that such a block is not user unsafe and
//! does not revoke the skip either.

#[trust::assume_total]
fn total(x: u32) -> u32 {
    x + 1
}

pub fn caller(x: u32) -> u32 {
    total(x)
}

#[trust::assume_total]
fn print_total(x: u32) {
    println!("{x}")
}

pub fn print_caller(x: u32) {
    print_total(x)
}

// Trust (r15, 2026-10-07): the `assume_total` revocation now asks the ONE
// enumeration of edges into unverified code (`unverified_edges`, rule
// `AssumedTotal`; `unverified_edge_kinds.rs` is the refusal side). None of these is
// such an edge, so each keeps its skip with no warning: a call to a local body, a
// read of a RUST `static` (const-evaluated and validated, it runs no code), a
// function pointer to a local body, and vtables minted for a local type at a local
// trait and for `u32` at core's `Debug`.
static TABLE: u32 = 7;

fn local_helper(x: u32) -> u32 {
    x / 2
}

pub trait LocalAct {
    fn act(&self) -> u32;
}

struct Local(u32);

impl LocalAct for Local {
    fn act(&self) -> u32 {
        self.0
    }
}

#[trust::assume_total]
fn edge_free(x: u32) -> u32 {
    local_helper(x) + TABLE
}

#[trust::assume_total]
fn local_fn_pointer() -> fn(u32) -> u32 {
    local_helper
}

#[trust::assume_total]
fn local_vtable() -> &'static dyn LocalAct {
    &Local(3)
}

#[trust::assume_total]
fn core_vtable() -> &'static dyn core::fmt::Debug {
    &3u32
}

pub fn edge_free_caller(x: u32) -> u32 {
    edge_free(x)
}

pub fn pointer_caller() -> fn(u32) -> u32 {
    local_fn_pointer()
}

pub fn vtable_callers() -> (&'static dyn core::fmt::Debug, &'static dyn LocalAct) {
    (core_vtable(), local_vtable())
}

// Trust (r20, 2026-10-07): controls for `unverified_edge_surface_and_consts.rs`.
// A sysroot callee at a local type whose impl surface names only foundational
// types (`Iterator::count::<Counter>`, `Item = u32`) is still held, and a vtable
// minted by CONST EVALUATION (a promoted) at core's `Debug` for `u32` is no edge
// either. (An `assume_total` body returning a local fn pointer read out of a `const` item or a promoted is
// revoked by the separate `requires` rule, not by the edge scan — measured on
// stage 1 of this change — so the local-fn-pointer constant controls are in
// `memory_safe_skip_const_local_fn_keeps_its_skip.rs`.)
struct Counter(u32);

impl Iterator for Counter {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.0 < 2 {
            self.0 += 1;
            Some(self.0)
        } else {
            None
        }
    }
}

#[trust::assume_total]
fn local_surface_count() -> usize {
    Counter(0).count()
}

#[trust::assume_total]
fn promoted_core_vtable() -> &'static dyn core::fmt::Debug {
    let p: &'static &'static dyn core::fmt::Debug = &(&3u32 as &dyn core::fmt::Debug);
    *p
}

pub fn const_callers() -> (usize, &'static dyn core::fmt::Debug) {
    (local_surface_count(), promoted_core_vtable())
}
