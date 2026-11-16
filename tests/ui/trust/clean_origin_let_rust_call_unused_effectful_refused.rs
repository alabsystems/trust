//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

//! **W5 increment 7 — A DEAD `let`-BOUND EFFECTFUL CALLEE IS STILL REFUSED.**
//! (`compiler/rustc_mir_transform/src/clean_origin_mir.rs`, the purity guard;
//! the sibling of `clean_origin_effectful_callee_refused.rs` for a binding the
//! body never reads.)
//!
//! The value temporary fixes the emitted COUNT and ORDER of a let-bound Rust
//! call; it cannot make the kernel's extensional callee model true of an
//! effectful callee. `let y := tick x; sub2 x x` is definitionally equal to
//! `sub2 x x` — the kernel identifies the body with one that never calls
//! `tick` — while this lane emits the call once (Trust's strict reading of a
//! dead `let`), and a user who writes `sub2 x x` directly gets no call. Two
//! def-eq-identical programs with different behaviour is not a proposition
//! the gate can state for `tick`, so PURITY remains the precondition, and the
//! guard walks EVERY plan node — a let-bound node read zero times included.
//!
//! `tick` reads and writes a `static` through an atomic RMW: impure. The guard
//! refuses `dead_effect` with the v7/D3 note naming the callee and the fix.
//! build-fail because nothing demands the minted body under `--emit metadata`.
//!
//! MODE CHANGED 2026-09-16, `build-fail` -> `check-fail`, and the refusal it
//! pins is UNCHANGED. The Clean-origin gate lives in the `optimized_mir`
//! PROVIDER for the Clean-origin def, so WHEN it runs is decided by who demands
//! that MIR. Until today nothing demanded it on an ordinary lane — a binary
//! compiled with `--emit metadata` never monomorphizes it, `run_required_analyses`
//! does not walk it, and `trust_ensure_whole_crate_verification` returns early
//! under `-Ztrust-verify=off` — so the first demand came from codegen and the
//! refusal arrived at BUILD time. `rustc_interface::passes` now demands it at the
//! analysis seam for every Clean-origin def this crate's Rust code NAMES, because
//! the island is a LANGUAGE surface (ruling v7/D1) and an artifact-lane flag
//! (`-Ztrust-ir-lower`) must not decide whether its gate runs at all.
//!
//! So the same fatal now arrives at CHECK time. `build-fail` additionally
//! requires the check build to PASS, which is now false — and was only ever true
//! because the gate had not run yet. Same diagnostic, same span, same text,
//! earlier. Nothing here is weakened: `check-fail` still demands the refusal, and
//! this file's annotations are untouched.

use std::sync::atomic::{AtomicU64, Ordering};

static COUNTER: AtomicU64 = AtomicU64::new(0);

fn tick(_x: u64) -> u64 {
    COUNTER.fetch_add(1, Ordering::SeqCst) + 1
}

fn sub2(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
}

clean {
    def dead_effect (x : UInt64) : UInt64 := let y := tick x; sub2 x x
}
//~^^ ERROR cannot be called from Rust
//~| NOTE may only call a PURE Rust fn

fn main() {
    let _ = dead_effect(3);
}
