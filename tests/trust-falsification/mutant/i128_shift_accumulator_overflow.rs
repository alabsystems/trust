#![crate_type = "lib"]
// MUTANT (i128 reduction soundness twin): summing i128 ELEMENTS directly — four values up to
// i128::MAX GENUINELY OVERFLOW. The recognizer rejects signed-i128 elements (no bounded
// per-element max), so NO BV accumulator bound is rendered. Pins that the BV bound-render is
// SELF-LIMITING (an unbounded signed reduction is never silently proved).
//
// Under `-Ztrust-policy=certify` (the gate's pinned policy; `-full` was this flag's
// pre-unification name) the undischarged per-add overflow MUST fail the build (exit 1).
// Measured 2026-08-04: certify rc=1 via the incompleteness header — a DECLINE, not a
// refutation; on the gate this is an honest UNCAUGHT MUTANT row. Under the default
// policy (policy B) the same decline exits 0 with the runtime check retained; the gate
// must never run this fixture under that default. See
// reports/2026-08-04-falsification-gate-first-end-to-end-run.md.
//
// 2026-08-15 — SUPERSEDED: THIS ROW IS NOW REFUTED, MEASURED END TO END.
// Everything above is pre-engine history: "an honest UNCAUGHT MUTANT row" was true
// when written and is FALSE now.
//
// The BV bound-render is still self-limiting and still renders nothing here — that
// part of the fixture's point stands. What is new is a SEPARATE, REFUTATION-ONLY
// lane, `trust_vcgen::generate_bounded_reduction_bmc_refutation_candidates`, which
// unrolls this loop to its statically known 4 iterations over UNBOUNDED SMT integers
// (no bitvectors at all — the width-128 IntToBv/BvShl bridge is documented to leave
// ay Unknown, so it is deliberately not used) and asks ay for a model.
//
// Measured on trustc d8059bf39 (== HEAD), gate invocation, exit code read without a
// pipe: rc=1, "Level 0 summary: 1 failed", and
//   [overflow:add] FAILED (trust-bmc-reduction-refute); counterexample: ...
// Full gate run: 269 PASS / 10 FAIL, this fixture PASS (refuted).
//
// The witness is `elem2 = -1, elem3 = i128::MIN`: t = -1, then -1 + i128::MIN
// underflows. Hand-checkable, and a real input.
pub fn f(a: &[i128; 4]) -> i128 {
    let mut t: i128 = 0;
    for &x in a {
        t += x;
    }
    t
}
