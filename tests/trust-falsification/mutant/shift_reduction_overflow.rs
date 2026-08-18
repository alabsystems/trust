#![crate_type = "lib"]
// MUTANT (shift-reduction soundness twin): `t += (x as u8) << 4` over `[u8;64]` with a
// `u8` accumulator GENUINELY OVERFLOWS (`64 * (some x<<4)` exceeds 255). The post-add
// sum bound `K*per_max` exceeds u8::MAX, so the structural arithmetic discharge does
// NOT fire. Pins that the bounded-reduction overflow discharge is SELF-LIMITING
// (proves only when the sum provably fits).
//
// Under `-Ztrust-policy=certify` (the policy the gate pins; this comment's original
// `-full` was the flag's pre-unification name) the undischarged overflow MUST fail
// the build (exit 1). Measured 2026-08-04: certify rc=1 with the incompleteness
// header — the verifier DECLINES, it does not refute (an overflow reachable only for
// some inputs is vanilla Rust semantics with the runtime check retained; there is no
// refutation engine for reduction overflow today). On the gate this row is therefore
// an honest UNCAUGHT MUTANT, not a false accept — see
// reports/2026-08-04-falsification-gate-first-end-to-end-run.md (RETRACTION and
// correction). Under the DEFAULT policy (policy B) the same decline exits 0 with the
// check retained; the gate must never run this fixture under that default.
//
// 2026-08-15 — SUPERSEDED: THIS ROW IS NOW REFUTED, MEASURED END TO END.
// Everything above the 2026-08-14 line is the pre-engine history and is kept only as
// that: "there is no refutation engine for reduction overflow today" was true when
// written and is FALSE now.
//
// `trust_vcgen::generate_bounded_reduction_bmc_refutation_candidates` unrolls this
// loop to its statically known 64 iterations and asks ay for a model of the exact
// violation formula; `refute_bounded_reduction_bmc_overflows` appends a `Failed`
// ArithmeticOverflow row on SAT-with-a-model ONLY.
//
// Measured on trustc d8059bf39 (== HEAD), gate invocation, exit code read without a
// pipe: rc=1, "Level 0 summary: 1 failed", and
//   [overflow:add] FAILED (trust-bmc-reduction-refute); counterexample: ...
// Full gate run: 269 PASS / 10 FAIL, this fixture PASS (refuted).
//
// The witness is `elem62 = 1, elem63 = 15`: t = 1<<4 = 16, then 16 + (15<<4) = 256,
// which exceeds u8::MAX. Hand-checkable, and a real input.
//
// NOTE for anyone re-deriving this: an earlier attempt (086b157aca) passed 20 unit
// tests on hand-built `VerifiableFunction`s and still did NOT fire here, because two
// recognition gates rejected the REAL extracted MIR (the always-true Option-tag
// precondition the `for` desugar mints, and the certified-dead `otherwise ->
// Unreachable` edge). Unit tests over synthetic shapes are not evidence that a
// recognizer fires on real MIR.
pub fn f(a: &[u8; 64]) -> u8 {
    let mut t: u8 = 0;
    for &x in a {
        t += (x as u8) << 4;
    }
    t
}
