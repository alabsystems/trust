//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off -Ztrust-clean-origin-mutate-emitter
//@ dont-check-compiler-stderr
//! **W5 (Lean-calls-Rust) — A WRONG RUST-CALL EMISSION MUST FAIL THE BUILD.**
//! (The `clean_origin_divergence_fails_build.rs` discipline, pointed at
//! `CleanOriginShape::RustCallChain`.)
//!
//! `-Ztrust-clean-origin-mutate-emitter` perturbs SIDE A only: the two
//! arguments of the emitted `Call(sub2, [a, b])` are swapped after the plan,
//! exactly like a real emitter bug — the body then computes `sub2 b a` for a
//! declaration that says `sub2 a b`. Side B (extractor, the separate-entry
//! reader, the reflection) is untouched, so the faithfulness gate still
//! compares two independent readings; and because `sub2` is a stuck `Opaque`
//! to the kernel, `is_def_eq` on the two applications is CONGRUENCE, which
//! separates them (`control_23::half_2` measures the same refusal on the fast
//! lane). The build fails with the gate's own message, options attached.
//!
//! build-fail, not check-fail, for the reason the projection twin records:
//! under `-Ztrust-verify=off` with `--emit metadata` nothing demands the
//! minted body; codegen does, through `main`'s call.
//!
//! What is NOT claimed: nothing about `sub2` — only that an emission which
//! does not denote the island's term is refused before it can link.
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

fn sub2(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
}

clean {
    def diff (a b : UInt64) : UInt64 := sub2 a b
}
//~^^ ERROR the emitted body could not be established to agree with the declaration

fn main() {
    // Never reached: the gate's fatal refusal fails the build first.
    let _ = diff(10, 3);
}
