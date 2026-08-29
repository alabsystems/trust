//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-timeout-ms=120000 -Copt-level=2
//@ dont-check-compiler-stderr
//! **The -O bare-`BinaryOp` wrapping boundary — what the 2026-08-20 crate-level
//! fix delivers, and exactly what it does not.**
//!
//! At -O the MIR inliner dissolves core's `wrapping_add` CALL into a bare
//! `Rvalue::BinaryOp(Add)` — the same rvalue form all user `+` takes in an
//! overflow-checks-off session. MIR defines that bare form as WRAPPING
//! (mod 2^w); the extractor keeps it distinct from the checked
//! (`CheckedBinaryOp` + Assert) and UB (`UncheckedBinaryOp`) forms. The rvalue
//! form alone is NOT the discriminator: measured on this binary at -O, a `main`
//! holding `let s = a.wrapping_add(b)` and one holding `let s = a + b` optimize
//! to the identical `_3 = Add(copy _1, copy _2)` (the wrapping one under
//! `scope (inlined core::num::<impl u64>::wrapping_add)`), yet only the plain
//! `+` draws an overflow obligation — so something other than the rvalue form
//! carries the distinction across the inliner.
//!
//! # What is FIXED at the crate level (unit-pinned, not by this fixture)
//!
//! trust-vcgen used to model the bare form as UNBOUNDED integer arithmetic
//! (`dest == a + b`), which is FALSE of every wrapping execution. That was
//! not just a havoc: conjoined into the `-full` assert-refutation lane —
//! where UNSAT of the panic-path formula is consumed as PROVED — it
//! false-PROVED `assert!(a + b >= a)`-shaped asserts that panic at runtime
//! (measured; see `trust_vcgen::generate::wrapping_binop_defs_tests::
//! wrapping_add_ge_lhs_false_prove_control`). The def is now the SAME
//! single-`Ite` modular reduction the marker-authenticated wrapping-call
//! model mints (`wrapping_binop_modular_ite`, one shared constructor), with
//! operand type-range facts; `Mul` and u128/i128 stay refused (dropped,
//! fail-closed) exactly like the call form.
//!
//! # What this fixture pins — MEASURED, not aspirational
//!
//! Verification-ON at -O over inlined-wrapping arithmetic still REFUSES this
//! crate, and NOT over the wrapping value model. Measured with the flags above
//! on stage2 ec4783d80:
//!
//!   * `opaque` — which contains no arithmetic at all — reports `0 proved,
//!     0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 1
//!     obligation(s)`. The strict error attributes it to an unproven
//!     panic-freedom obligation for a call to an absent callee (a std/extern
//!     function whose body is not in the lowered bundle); the only call in
//!     `opaque` is `std::hint::black_box`.
//!   * `main` reports `0 proved, 2 failed, 0 unknown, 0 timed out,
//!     1 runtime-checked out of 3 obligation(s)`. The two failures are the two
//!     guarded asserts below: the verifier does not model what `opaque`
//!     returns, so it counterexamples them with values that ignore
//!     `opaque(3) == 3` (printed: `a = 1, b = 0, s = 7`). No overflow row is
//!     charged for the inlined wrapping ops — a control `main` differing only
//!     in `a.wrapping_add(b)` vs `a + b` measures one obligation vs two, the
//!     extra one failed.
//!
//! So the boundary that remains here is the opaque callee, not wrapping
//! arithmetic. The differential evidence for the value-model fix itself (wrap
//! witness feasible, unbounded encoding gone, Mul still refused, checks-ON
//! shape untouched) lives in the trust-vcgen unit suite named above, which
//! does not need a compiler rebuild.

#[inline(never)]
// MEASURED (2026-08-22, stage2 ec4783d80): the one row here is panic-freedom
// for the absent callee `std::hint::black_box`, runtime-checked, which strict
// refuses. It is NOT an overflow row — `opaque` has no arithmetic. This pin
// flips to run-pass when absent-callee panic-freedom is closed; do not flip it
// by weakening strict.
fn opaque(x: u64) -> u64 {
//~^ WARN Trust Level 0 safety verification incomplete
//~| ERROR Trust strict verification failed
    std::hint::black_box(x)
}

fn main() {
//~^ ERROR Trust Level 0 safety verification incomplete
//~| ERROR Trust strict verification failed
    let a = opaque(3);
    let b = opaque(4);
    // Guarded window: no operation below can overflow at runtime. The asserts
    // still fail statically — `a` and `b` come from `opaque`, whose return the
    // verifier does not model.
    if a <= 10 && b <= 10 {
        // At -O this call is inlined to a bare `Rvalue::BinaryOp(Add)`.
        let s = a.wrapping_add(b);
        assert!(s == 7, "guarded wrapping_add must equal the plain sum");
        let d = s.wrapping_sub(b);
        assert!(d == a, "guarded wrapping_sub must invert the add");
    }
}
