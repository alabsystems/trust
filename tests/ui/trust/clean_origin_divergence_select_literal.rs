//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off -Ztrust-clean-origin-mutate-emitter
//@ dont-check-compiler-stderr
//! **R2/C9 — A WRONG SELECT-VS-LITERAL EMISSION MUST FAIL THE BUILD.**
//!
//! The literal-compare twin of `clean_origin_divergence_select.rs`. Under
//! the knob, the emitted diamond's `SwitchInt` targets are swapped — the
//! polarity inversion — so the emission returns `b` below the literal where
//! the declaration says `a`. Side B is untouched; the gate refuses with its
//! own fatal, observed from the driver.
//!
//! The crate-level dual lives in the C9 control suite
//! (`control_7_select_literal_emitter_mutation.rs`); this fixture is the
//! same property from the driver.
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
        def clamp10 (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b
    }
    //~^^ ERROR the emitted body could not be established to agree with the declaration
}

fn main() {
    // Never reached: the gate's fatal refusal fails the build first.
    let _ = crate::m::clamp10(9, 77);
}
