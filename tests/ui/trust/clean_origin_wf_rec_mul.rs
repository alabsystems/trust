//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **§R6 ACCEPTANCE — FACTORIAL IS EMITTABLE AND CALLABLE.**
//!
//! The sibling fixture `clean_origin_wf_rec.rs` runs `countdownSum`, whose
//! non-zero arm is `n + rec`. This one runs `fact`, whose non-zero arm is
//! `n * rec`, and that single character is the whole of what the compiler
//! grew: the `nat.mul` selection row.
//!
//! # Why this is a small landing and not a re-plumbing
//!
//! The emitted MIR is `countdownSum`'s, block for block, with ONE
//! authenticated callee changed — `trust_bignum::arith::<impl
//! trust_bignum::Nat>::mul` in place of `…::add` — because `+` and `*` lower
//! through the SAME arm of `ArmLowerer` and differ only in which
//! `PrimitiveCallee` names them. The reflection is the same shared descent
//! (`render_rec_node`) emitting the row's own kernel constant. The gate route
//! is unchanged: `check_faithful_wf_functional`, the same borrow of side A's
//! decrease proofs into side B's sentinel slots, the same closure audit.
//!
//! # The kernel probe ran BEFORE the producer was written
//!
//! Side B renders raw `Nat.mul`; the elaborator emits the surface
//! `HMul.hMul Nat Nat Nat instHMulNat`. `r6_nat_mul_probes` q7 measured the
//! kernel identifying the two (`a * b = Nat.mul a b := rfl` ADMITS) and
//! SEPARATING the near one (`a * b = Nat.add a b := rfl` is REFUSED). That
//! order is the discipline three earlier spelling-gap defects were caught for
//! skipping: `Expr::nat_lit(5)` vs `OfNat.ofNat`, `Nat.beq` vs `BEq.beq`, and
//! the `Nat.lt`/`Nat.decLt`/`Nat.sub` trio that made the whole R2 lane
//! unreachable while every in-crate test was green.
//!
//! # DELIBERATELY NOT HERE
//!
//!   * **`gcd`.** Still not callable — **and, measured 2026-08-25, NOT for the
//!     reason the sibling fixture states.** `first-party/clean` gained
//!     two-parameter well-founded recursion with a one-parameter measure in
//!     R3/R4, both of which are in the current pin: `def gcd (a b : Nat) : Nat
//!     := if h : 0 < b then gcd b (a % b) else a  termination_by b`
//!     ELABORATES and kernel-checks. What refuses it is THIS compiler's
//!     single-parameter fix-spine reader. A SUBTRACTIVE `gcd` does not route
//!     around that: it decreases only in `a + b`, and a two-parameter MEASURE
//!     is refused island-side by name. See `r6_nat_mul_probes` q1/q2/q3.
//!   * **`/` and `%`.** Outside the vocabulary and staying there: Clean's
//!     `Nat.div`/`Nat.mod` are TOTAL where the Rust realization PANICS at a
//!     zero divisor, and commit `fa788aab89` measured the faithfulness gate
//!     BLIND to that divergence. `r6_nat_mul_probes` q10 pins the refusal.
//!
//! SMALL INPUTS ON PURPOSE, same as the sibling: the emitted self-call form
//! recurses O(value) deep and each frame allocates a bignum.
//!
//! THE VALUES BELOW ARE PROBE-PINNED, not invented: `r6_nat_mul_probes` q11
//! closes `fact 0/1/3/5/8 = 1/1/6/120/40320` by `rfl` at the real kernel, with
//! `fact 5 = 121` as the refuting control. What runs here is the EMITTED
//! binary computing them.

extern crate trust_bignum;

clean {
    def fact (n : Nat) : Nat := if h : 0 < n then n * fact (n - 1) else 1
    termination_by n
}

fn nat(value: u64) -> trust_bignum::Nat {
    trust_bignum::Nat::from_u64(value)
}

fn main() {
    for (input, expected) in [(0u64, 1u64), (1, 1), (3, 6), (5, 120), (8, 40320)] {
        let out = fact(nat(input));
        assert_eq!(
            out.to_u64(),
            Some(expected),
            "fact({input}) must compute {expected} through the emitted well-founded \
             recursion"
        );
    }

    // The zero arm of the emitted zero test, on its own: `0! = 1`, not `0`.
    // This is the row that separates the `nat.mul` body from the `nat.add`
    // one at RUNTIME — a `+`-shaped emission would return 0 here.
    let out = fact(nat(0));
    assert_eq!(out.to_u64(), Some(1), "fact(0) must take the zero arm and yield 1");
}
