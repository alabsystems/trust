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
//!   * `main` reports `0 proved, 0 failed, 0 unknown, 0 timed out,
//!     3 runtime-checked out of 3 obligation(s)` (re-measured 2026-08-30,
//!     stage1 at main tip). The two guarded asserts used to come back as
//!     FAILED with a counterexample over values the verifier does not model
//!     (`opaque` returns havoc'd: printed `a = 1, b = 0, s = 7` — not a real
//!     execution, since `opaque(3) == 3` makes both asserts pass at runtime).
//!     bc65b2ca7d/017a2a2af5 introduced and 730b8d6cee deliberately RETAINED
//!     the Assertion-kind proof-only bridge arm
//!     (`bridge_ay_verdict_is_admissible`): a generic ay SAT on a user
//!     `assert!` whose formula ranges over values no execution pins is not
//!     admissible as a source refutation, so those two rows are demoted
//!     Failed -> Unknown, and with their runtime fallback they land in the
//!     runtime-checked bucket. Under the ratified completeness-gap policy a
//!     runtime-checked-only gap is non-fatal, so the Level 0 incomplete
//!     diagnostic for `main` is now a WARN (the strict error below still
//!     fails the build — nothing turned green). No overflow row is
//!     charged for the inlined wrapping ops — a control `main` differing only
//!     in `a.wrapping_add(b)` vs `a + b` measures one obligation vs two.
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
// RE-MEASURED (2026-08-30, composed stage with the held-refutation stamp): the
// L0 header is ERROR again, as the stamp's audit predicted. main's asserts on
// `opaque`-derived values carry live bridge SAT counterexamples; those rows
// were HELD (proof-only Assertion bridge) and rode runtime-check tolerance to
// a WARN. The stamp denies that tolerance (GapToleranceDenial::
// RowRefutationHeld), so a held refutation is fatal. The old a=1,b=0,s=7
// counterexample over havoc'd opaque() returns was a FALSE refutation and
// stays demoted; these are the live ones. `opaque` itself keeps WARN: its one
// row is absent-callee panic-freedom, runtime-checked, no refutation held.
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
