//@ needs-trust-verify
//@ edition: 2021
//@ revisions: debug o2plain
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[o2plain] compile-flags: -Copt-level=2
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
//! Trust (D8-P0, 2026-09-23): the POSITIVE CONTROLS of the
//! `[unsafe:validity-transmute]` creation row
//! (`validity_transmute_creation_row.rs` holds the refusals).
//!
//! The row charges every transmute whose target is not INERT
//! (`transmute_target_carries_invariant` in
//! `compiler/rustc_mir_transform/src/trust_verify/validity_transmute.rs`). These
//! bodies must keep verifying, each for a stated reason — measured rc=0 on the
//! stage-1 `trustc` of 2026-09-23 at both opt-levels. (-O parity, 2026-09-25:
//! `opt` now states `-Zmir-opt-level=2`, the only session that still inlines;
//! `o2plain` pins the plain `-Copt-level=2` default, which runs the `-O0` MIR
//! pipeline.)
//!
//! * `sign`, `same`: integer targets are inert (every bit pattern is a value);
//!   `same` is also the identity `InstSimplify` erases from the MIR, so it pins
//!   that the HIR half does not charge an inert identity either.
//! * `to_raw`: a raw pointer to a SIZED pointee is inert — a later deref keeps its
//!   own `[unsafe:sep:*]` row; the SOURCE being a reference is irrelevant.
//! * `fresh_box`: `Box::new` is not a transmute in user scope; the only
//!   transmute in this body is rustc's `ElaborateBoxDerefs` `NonNull -> *const`
//!   (inert target), at both opt-levels.
//! * `param_box`: the Box-parameter validity root, unchanged.
//!
//! The control for the SYSROOT-INLINE exemption is
//! `policy_b/println_release_opt_run_pass.rs` (`-Copt-level=2`, verified): its
//! optimized `main` carries std's inlined `fmt::rt::Argument` packing
//! (`NonNull<()>`, the `unsafe fn(NonNull<()>, &mut Formatter)` table) — non-inert
//! targets whose nearest inlined instance is an authenticated sysroot def. If
//! that fixture starts failing on `[hardened_unsafe_operation]`, the exemption
//! has broken.
//! * `debug` only — `vec!` and `println!` (both refused at `-O2` today for
//!   reasons unrelated to this row): at `-O0` neither lowers to a user-scope
//!   transmute into a non-inert type.
//!
//! What this file cannot hold: an async control. The `.await` lowering's two
//! compiler transmutes (`&mut Context` <-> `ResumeTy`'s `NonNull<Context>`) are
//! exempt structurally, and the fixtures that pin that are the already-passing
//! async ones (`once-reentrancy/async_body_ok.rs`,
//! `trust_ir_lower_await_pure_carrier.rs`, `trust_ir_lower_await_suspend.rs`):
//! they must stay green. A standalone `async fn` pair is refused today by the
//! coroutine executor-protocol premise, so it cannot be a control here.

use std::mem::transmute;

pub fn sign(x: u32) -> i32 {
    unsafe { transmute::<u32, i32>(x) }
}

pub fn same(x: u32) -> u32 {
    unsafe { transmute::<u32, u32>(x) }
}

pub fn to_raw(p: &u32) -> *const u32 {
    unsafe { transmute::<&u32, *const u32>(p) }
}

pub fn fresh_box() -> u32 {
    let x = Box::new(3u32);
    *x
}

pub fn param_box(b: Box<u32>) -> u32 {
    *b
}

#[cfg(debug)]
pub fn small_vec() -> usize {
    let v = vec![1u32, 2, 3];
    v.len()
}

#[cfg(debug)]
pub fn print(x: u32) {
    println!("{x}")
}
