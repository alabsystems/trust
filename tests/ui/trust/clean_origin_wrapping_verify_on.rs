//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-timeout-ms=120000 -Copt-level=0
// -Copt-level=0 is LOAD-BEARING, not a convenience: compiletest compiles
// run-pass tests with -O, and at -O the MIR inliner dissolves core's tiny
// wrapping_add CALL into Rvalue::BinaryOp. UPDATE 2026-08-20: the VALUE model
// no longer refuses that residual form — trust-vcgen now defines a bare
// integer BinaryOp Add/Sub by the SAME modular-Ite the call model mints
// (`wrapping_binop_modular_ite`, one shared constructor; previously the def
// was the unbounded `a + b`, which was not merely a havoc but a measured
// FALSE-PROVE vector in the -full refute lane — see
// `trust_vcgen::generate::wrapping_binop_defs_tests`). -Copt-level=0 REMAINS
// load-bearing for this fixture even so, for two reasons the crate-level fix
// does not touch: (1) this fixture pins the SUMMARY lane (a verified caller
// proving through the call boundary), which requires the call to still BE a
// call when the verifier reads the MIR; and (2) the L0 safety lane still
// mints an ArithmeticOverflow obligation for every bare integer Add/Sub/Mul
// (generate/safety.rs, direct-binop arm — deliberate policy), which the
// genuinely-wrapping `wsum(u64::MAX, 1)` refutes once inlining erases the
// wrapping-call provenance. Lifting THAT needs compiler-side work (inliner
// provenance or pre-inlining extraction), not a vcgen model.
// (the generous timeout is NOT decoration: under parallel compiletest load the
// in-process solver's default budget intermittently lapses on the modular-Ite
// obligation, flipping a PROVED row to timed-out — measured flaking between
// consecutive bless runs on an otherwise identical tree)
//@ run-pass
//@ dont-check-compiler-stderr
//! **I5 — A CLEAN-ORIGIN BODY WITH A CALL TERMINATOR, VERIFICATION ON.**
//!
//! `clean_origin_verify_on.rs` pinned that the verification walks survive a
//! Clean-origin def at all. This file is the same measurement for the
//! `WrappingBinOp` shape, and it is NOT redundant with it: a projection body
//! is call-free, while these bodies contain a **Call terminator to core's
//! `u64::wrapping_add`** — so the R1 call-graph scan
//! (`trust_mir_direct_local_callees`) and every verify walk traverse a
//! Clean-origin body with an edge in it. The scan's `DefId::as_local()`
//! filter drops the core callee (it is not local by construction — the
//! authenticated primitive lives in the `Sized`-lang-item crate), so no SCC
//! node or adjacency edge appears.
//!
//! # GREEN AS OF 2026-08-20 — the WrappingBinOp summary lane
//!
//! This fixture is `run-pass`: it compiles under verification-ON default
//! policy, runs, and `main`'s asserts VERIFY. The boundary its first life
//! pinned — the caller's obligation failing closed because the VC lane
//! havocked the call — is closed by exactly the increment its old header
//! demanded ("when cross-authority call modeling lands, this fixture flips to
//! run-pass"), not by a weakened strict policy and not by a hand-written
//! contract.
//!
//! **The summary's authority chain** is `clean_origin_verify_on.rs`'s, with
//! one more step: kernel gate → plan of record
//! (`clean_origin_call_model_of_record`) → definitional summary — and for this
//! shape the summary's encoding is NOT free. It must be THE EXTRACTOR'S OWN
//! wrapping encoding, the single-`Ite` modular reduction
//!
//! ```text
//! _0 == ite(a + b >= 2^64, a + b - 2^64, a + b)
//! ```
//!
//! (`trust_vcgen::clean_origin_wrapping_binop_postconditions`, pinned
//! unit-test-for-unit-test against `wrapping_call_assert_model` — the model
//! trust-vcgen mints when an ordinary extracted Rust body calls the same
//! primitive). Panic-freedom rides separately: the emitted body's one call is
//! to the emitter-selected, marker-authenticated total primitive with
//! `UnwindAction::Unreachable`, so the call is compiler-total, no assumption
//! row in any mode.
//!
//! # Why `u64::MAX` — this fixture is ALSO the wrong-encoding control
//!
//! `wsum(u64::MAX, 1)` returns **0**, the WRAPPED value, and the assert below
//! claims exactly that. A summary that encoded the body as unbounded integer
//! arithmetic (`_0 == a + b`, the classic false-PROVE encoding) would pin the
//! dest to `2^64` and REFUTE this assert — so this fixture failing is what a
//! wrong-semantics summary looks like, and `clean_origin_wrapping_wrong_claim.rs`
//! is the opposite control (a wrong CALLER claim must still be refuted). The
//! pair can only be green together if the summary carries mod-2^64 semantics.
//! `winc` additionally covers the in-range NUMERAL operand spelling (probes
//! a4–a6): `winc(u64::MAX) == 0` for the same wrap-around reason.
//!
//! Nothing here claims proof authority for the emitted bodies — the injected
//! summary is a compiler-composed derivation from the kernel gate's plan of
//! record (`Trusted`, not `Certified` — see the Clean-origin rows of
//! `docs/TCB.md`).

mod m {
    clean {
        def wsum (a : UInt64) (b : UInt64) : UInt64 := a + b
        def winc (a : UInt64) : UInt64 := a + 1
    }
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    //~| WARN Trust verification advisory
    // (the retained runtime check on the third obligation surfaces as two
    // advisory WARNs under JSON diagnostics; strict does not fire because the
    // two value asserts are PROVED and the retained check is the assert
    // machinery's own, graded runtime-checked — the boundary the summary lane
    // does not claim)
    // Runtime calls, verification ON. `assert!`, not `assert_eq!`, and no
    // `println!` — MEASURED boundaries of the L0 lane that are NOT about
    // Clean-origin calls (see clean_origin_verify_on.rs for both).
    let s = m::wsum(u64::MAX, 1);
    // The WRAPPED value: (2^64 - 1) + 1 ≡ 0 (mod 2^64). An unwrapped integer
    // summary would REFUTE this — see the header.
    assert!(s == 0, "the emitted body must be the wrapping add the Clean `def` denotes");
    let w = m::winc(u64::MAX);
    assert!(w == 0, "the numeral-operand spelling must carry the same mod-2^64 semantics");
}
