//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **§6f LANDING 2 — THE CONSTANT EMISSION, RUN.**
//! (`CleanOriginShape::ConstantUint`; `crates/trust-clean-origin/src/emit.rs`,
//! emitted by `build_constant_body` in
//! `compiler/rustc_mir_transform/src/clean_origin_mir.rs`.)
//!
//! This is the shape landing 1 ranked FIRST on its MISS list and refused, on
//! the corpus reading that `ConstantUint` was the shape kernel defeq rejected.
//! That reading was superseded by measurement:
//! `fragment_widening_probes::probe_e`/`probe_e2` showed the bare kernel
//! comparison ADMITS it in both numeral spellings, and `probe_e3` located the
//! real defect UPSTREAM of defeq, in the arity-erasing
//! `ConstantUint -> admit_constant_function` ROUTING. Landing 2 repaired the
//! routing after measuring the repair first
//! (`crates/trust-clean-origin/tests/landing2_selection_probes.rs`).
//!
//! What this fixture pins that the fast lane cannot:
//!
//! * `six()` — the NULLARY declaration really becomes a callable `fn() -> u64`.
//!   Every fast-lane control hands `admit_lowering` a hand-built
//!   `VerifiableFunction`; only a real compilation exercises the mint feeding
//!   `fn_sig` with an EMPTY parameter list, `build_constant_body` emitting a
//!   one-local body, and the extractor reading it back.
//! * `k(x)` — the same declaration shape behind an IGNORED binder. The
//!   recognizer reports the same `ConstantUint` for both
//!   (`probe_e3`: the arity is ERASED), so a compilation in which BOTH link and
//!   return 6 is the end-to-end statement that the arity is bound elsewhere —
//!   on side B, where `admit_lowering` compares `arg_count` against the
//!   signature's arity and the reflection's lambda count is that same count.
//! * `b8()` at `UInt8` — the width comes from the plan's result carrier and the
//!   reflection's domain from the emitted return type, so a non-u64 width is
//!   measured rather than assumed.
//! * `C`/`CK` — CTFE goes through `mir_for_ctfe`, whose only source of a
//!   Clean-origin body is the GATED emission, at both arities.
//!
//! `-Z trust-verify=off` is the point, not a convenience: the faithfulness
//! gate is a compilation-correctness check, deliberately NOT behind any
//! verification switch, and this fixture would be worthless if the flag could
//! disable the machinery it measures.

mod m {
    clean {
        def six : UInt64 := 6
        def k (x : UInt64) : UInt64 := 6
        def b8 : UInt8 := 200
    }
}

// CTFE at BOTH arities: the const lane's only source of a Clean-origin body is
// the gated emission, and the nullary case is the one that never existed
// before this landing.
const C: u64 = crate::m::six();
const CK: u64 = crate::m::k(99);

fn main() {
    assert_eq!(m::six(), 6, "the nullary constant emission must return its numeral");
    assert_eq!(m::k(0), 6, "a constant behind an ignored binder ignores it");
    assert_eq!(m::k(u64::MAX), 6, "…for every argument, which is what 'ignored' means");
    assert_eq!(m::b8(), 200u8, "the constant emission is at the declaration's own width");
    assert_eq!(C, 6, "CTFE of the nullary emission must agree with the runtime value");
    assert_eq!(CK, 6, "CTFE of the unary emission must agree too");
}
