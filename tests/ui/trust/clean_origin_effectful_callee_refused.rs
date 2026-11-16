//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

//! **Clean-origin PURITY GUARD — an effectful Rust callee is refused (soundness).**
//! (`compiler/rustc_mir_transform/src/clean_origin_mir.rs`, `rust_callee_is_pure`;
//! the fix of 2026-09-14.)
//!
//! A Clean `def` treats every Rust callee it names as a PURE kernel value: the
//! faithfulness gate is kernel definitional equality against the declaration
//! term, and the kernel is a PURE calculus — `tick x` denotes ONE value however
//! many times it is written. It cannot see that the emitted `tick` reads and
//! writes a `static` through an atomic. So a `RustCallChain` over an effectful
//! callee is a WRONG BINARY the gate cannot catch: `let y := tick x; sub2 y y`
//! and `sub2 (tick x) (tick x)` are definitionally equal (zeta), and the kernel
//! reads both as `sub2 v v = 0` — yet this lane emits ONE `tick` call for the
//! first (W5 increment 7's value temporary) and TWO for the second (values 1
//! and 2, `sub2(1, 2) = u64::MAX`). Two def-eq-identical programs with
//! different behaviour is not a proposition the gate can state for `tick`, so
//! purity is the precondition. Per-shape single-evaluation cannot close
//! this — the unsoundness is the effectful callee, not any one `let` shape — so
//! the purity guard refuses ANY Clean `def` whose Rust callee is not provably
//! pure, at MIR time where the callee's MIR is available.
//!
//! `tick` reads a `static` (`COUNTER`) and calls an atomic RMW, so it is impure;
//! the guard refuses `dup_let` fatally with a v7/D3 note that names the callee
//! and the fix. This is INDEPENDENT of the verification mode — the guard is a
//! compilation-correctness check, not a proof obligation — which is why this
//! test runs with `-Z trust-verify=off`, exactly as the unconditional
//! faithfulness gate does.
//!
//! **`build-fail`, NOT `check-fail`, and the reason is monomorphization.** The
//! guard lives in `clean_origin_mir.rs`, the sole constructor of a Clean-origin
//! `Body`, so it fires only when something actually asks for that body's MIR.
//! Nothing does until `main` reaches `dup_let` through mono collection.
//! Measured 2026-09-15 on this file, fresh output dir each run:
//!
//!   trustc --emit metadata                 guard SILENT, exit 0   (12/12 runs)
//!   trustc --crate-type lib                guard SILENT, exit 1   (other error)
//!   trustc            (infers bin + main)  guard FIRES,  exit 1
//!
//! `check-fail` runs compiletest's check build, which is `--emit metadata` — the
//! first row. So this fixture could never have passed as written: it was landed
//! `check-fail` and was red from that moment. `build-fail` builds the binary,
//! which is the third row, and it must NOT carry a `--crate-type` override:
//! forcing `lib` puts it back in the second row and the guard stays silent.
//!
//! The consequence worth knowing, and NOT fixed here: `cargo check` is green on
//! a program `cargo build` refuses. That is a gate-timing gap, not a soundness
//! hole — the wrong binary is still never emitted, here or in a downstream
//! crate that calls `dup_let`, because emitting it is exactly what trips the
//! guard. Firing earlier would need the callee's MIR before mono collection
//! asks for it, which is why the guard sits where it does; the sibling
//! `clean_origin_rust_call_contracted_callee_refused` IS `check-fail` precisely
//! because its guard is at resolve time and needs no MIR.
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

// EFFECTFUL: reads/writes a `static` via an atomic RMW.
fn tick(_x: u64) -> u64 {
    COUNTER.fetch_add(1, Ordering::SeqCst) + 1
}

fn sub2(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
}

clean {
    def dup_let (x : UInt64) : UInt64 := let y := tick x; sub2 y y
}
//~^^ ERROR cannot be called from Rust
//~| NOTE may only call a PURE Rust fn
// (annotated from OUT here, not with a trailing comment on the `def` line:
// that line is parsed by Clean, and `//` is not a Clean comment.)

fn main() {
    let _ = dup_let(0);
}
