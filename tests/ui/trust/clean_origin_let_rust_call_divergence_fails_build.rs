//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off -Ztrust-clean-origin-mutate-emitter
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **W5 increment 7 — A DUPLICATED LET-TEMP EVALUATION MUST FAIL THE BUILD.**
//! (The `clean_origin_rust_call_divergence_fails_build.rs` discipline, pointed
//! at the let-bound Rust-call temporary.)
//!
//! `-Ztrust-clean-origin-mutate-emitter` perturbs SIDE A only: the emitted
//! body's one `Call(dbl)` into the temporary read twice by `sub2` is CLONED
//! into a fresh local, and the second read is pointed at the clone — the body
//! then calls `dbl` twice for a declaration whose `let` evaluates it once. This
//! is exactly the divergence the kernel cannot see: `let y := dbl x; sub2 y y`
//! and `sub2 (dbl x) (dbl x)` are definitionally equal, so `is_def_eq` alone
//! would ACCEPT the duplicated body. The refusal must come from the STRUCTURAL
//! half — side B reads three `Call` blocks back where the plan holds two nodes,
//! and `admit_rust_call_chain_lowering`'s node-for-node comparison refuses
//! before the kernel is consulted (`control_27::half_2` measures the same on
//! the fast lane). The build fails with the gate's own message, options attached.
//!
//! build-fail, not check-fail: under `-Ztrust-verify=off` with `--emit
//! metadata` nothing demands the minted body; codegen does, through `main`'s call.
//!
//! What is NOT claimed: nothing about `dbl` or `sub2` — only that an emission
//! which evaluates a let-bound call a different number of times than the
//! declaration is refused before it can link.
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

fn dbl(x: u64) -> u64 {
    x.wrapping_add(x)
}

fn sub2(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
}

clean {
    def dup_pure_let (x : UInt64) : UInt64 := let y := dbl x; sub2 y y
}
//~^^ ERROR the emitted body could not be established to agree with the declaration
//~| NOTE 3 call(s) emitted for 2 planned

fn main() {
    let _ = dup_pure_let(5);
}
