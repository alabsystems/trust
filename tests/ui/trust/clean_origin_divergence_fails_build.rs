//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off -Ztrust-clean-origin-mutate-emitter
//@ dont-check-compiler-stderr
//! **R3 END-TO-END RED (#65, C3) — A WRONG EMISSION MUST FAIL THE BUILD.**
//! (`docs/plans/2026-08-02-v7-island-parse-and-produce.md` §4: "Acceptance is
//! the RED case"; deferred by the R3 checker commit until a compiler-visible
//! way to force a diverging emission existed. This is that fixture.)
//!
//! `-Ztrust-clean-origin-mutate-emitter` perturbs SIDE A only — the emitted
//! body's projection is swapped to the OTHER argument after the plan, exactly
//! like a real emitter bug. Side B (extractor, admitters, recognizer) is
//! untouched, so the faithfulness gate still compares two independent readings,
//! and the kernel's definitional-equality judgment is what refuses: the
//! emission denotes `b` where the declaration says `a`.
//!
//! WHY build-fail, NOT check-fail — MEASURED (2026-08-20): under
//! `-Ztrust-verify=off` with `--emit metadata`, NOTHING demands the minted
//! body — no codegen, and the verify pass (which walks `mir_keys` and would
//! demand it) is off — so the gate has no occasion to run and the compile
//! exits 0. That is sound, not a hole: a metadata-only build materializes no
//! runnable body either. The gate guards every path that DOES materialize one:
//! codegen (this fixture: mono collection reaches `g` through the call and
//! demands `optimized_mir`, where the gate refuses), CTFE, and the verify
//! pass's own walk under `-Ztrust-verify=on`. The original draft of this
//! fixture claimed check-fail sufficed via the analysis-side drops ensure —
//! wrong: that ensure fires under verify=on (which is how the mint's ICEs
//! surfaced in C0), not in a vanilla metadata build.
//!
//! The dual control lives at crate level
//! (`trust-clean-origin/tests/control_3_clean_origin_emitter_mutation.rs`);
//! this fixture is the same property observed from the driver: the BUILD fails,
//! with the gate's own message, options attached per v7/D3.
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

mod m {
    clean {
        def g (a : UInt64) (b : UInt64) : UInt64 := a
    }
    //~^^ ERROR the emitted body could not be established to agree with the declaration
}

fn main() {
    // Never reached: the gate's fatal refusal fails the build first. (Direct
    // call — the mint plants `Visibility::Public`; the parity rationale lives
    // in clean_origin_call_parity.rs.)
    let _ = crate::m::g(6, 7);
}
