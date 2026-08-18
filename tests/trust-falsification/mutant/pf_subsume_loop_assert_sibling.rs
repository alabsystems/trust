#![crate_type = "lib"]
// MUTANT (FALSE PROOF regression, 2026-08-14 — the `while` shape).
//
// `f(0)`, `f(1)`, `f(2)`, and `f(3)` all panic: the loop runs `i = 0,1,2,3` and
// `assert!(n != i)` fails on the matching iteration. The verifier MUST refuse
// this (exit 1).
//
// This is the exact shape that survived the falsification corpus. Under
// `-Ztrust-policy=certify` it reported "2 proved, 0 failed, 0 unknown" and
// exited 0. The two rows were:
//   * `vc:…:arithmetic_safety:0` — the `i += 1` overflow, genuinely proved by
//     the `interval` solver and kernel-certified;
//   * `vc:…:assertion:panic-freedom:0` — the synthesized whole-function
//     aggregate, "proved" by `trust-structural-subsumption`.
// The subsumption discharged the aggregate from "every OTHER row is a static
// proof". The overflow proof says NOTHING about `assert!(n != i)`, and the
// assert has no per-site row at all: a diverging `panic!`/`assert!` Call is
// never a counted per-site obligation, so the bridge folds it into that very
// aggregate. The supporting conjunction therefore never covers the panic it is
// asked to rule out. That lane is gone; the aggregate now stays unproved.
//
// The LOAD-BEARING detail is the sibling row: the straight-line twin
// (`mutant/cursor_clamp_assert.rs`) is correctly refuted, and without the
// `i += 1` the empty-conjunction guard already refuses. Keep the arithmetic
// sibling — it is the whole test.
pub fn f(n: u8) -> u8 {
    let mut t = 0u8;
    let mut i = 0u8;
    while i < 4 {
        assert!(n != i);
        t ^= i;
        i += 1;
    }
    t
}
