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
// 2026-09-10 — REGRESSED AND RESTORED. Root cause pinned by bisecting two BUILT
// compilers with the gate's exact invocation: `acb08e7616` (atpkg, 2026-08-21 14:40)
// still prints `Level 0 summary: 1 failed` + `[overflow:add] FAILED
// (trust-bmc-reduction-refute)` here, while `c2031f179` (2026-09-10) prints `0 failed`.
// Exactly one commit in that range touches the lane: `4ca0cb0eac` (2026-08-21 20:51) deleted
// the `otherwise`-edge argument in `crates/trust-vcgen/src/generate/bmc_reduction.rs`
// (`bmc_terminator_succs`), so the `SwitchInt`'s `otherwise -> Unreachable` block
// re-entered the reachable set and `body_is_straight_line_reduction`'s terminator
// allowlist refused the function. Its objection was right — the deleted code keyed on
// the caller-constructible `exhaustive_enum_unreachable` bit — and it named the bar for
// restoring it: prune only from locally rederived, subject-bound type evidence. That is
// what the restored `switch_otherwise_is_dead_by_declared_enum_type` supplies: the bit is
// never read; the scrutinee must be a `Discriminant` read of a place whose DECLARED type
// is an enum, with the case set exactly that enum's declared discriminant set. Every one
// of the ~40 synthetic unit tests stayed green across the whole regression — the trap this
// header already warns about — so the guard is now
// `crates/trust-vcgen/tests/bmc_reduction_real_mir.rs`, over the compiler's OWN dumped MIR.
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
