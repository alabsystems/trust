//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **R2 ACCEPTANCE — WELL-FOUNDED RECURSION IS EMITTABLE AND CALLABLE.**
//! (§6e MEASUREMENT NOTE + §6e ESCAPE CLOSED,
//! `docs/design/2026-08-04-two-language-compiler-architecture.md`.)
//!
//! The island below is BYTE-CLASS-IDENTICAL to the `countdownSum` that
//! `recursion_boundary_probes.rs` measured **ADMITTED** by the island
//! elaborator — its value IS
//! `@WellFounded.fix.{1,1} Nat (fun _ => Nat) (fun a b => Nat.lt a b)
//! (WellFounded.intro … Acc.rec … Nat.accNatLt …) (fun x rec => dite …)`,
//! the elaborator's phase-1 WF lowering — and REFUSED by the planner. That
//! refusal is flipped EXPLICITLY in the change that lands the R2 lane.
//! Nothing about the declaration changed; the compiler grew:
//!
//!   * the `WellFoundedNatRec` plan/recognise arms — side A's fix spine
//!     parsed in BOTH the eta-expanded and the eta-contracted spelling (the
//!     §6e MEASUREMENT NOTE records a design that parsed neither), its
//!     functional read into the closed `RecBodyExpr` vocabulary, and its
//!     termination evidence required to be a `WellFounded.fix`-headed value
//!     of a `FullKernelCheck` declaration;
//!   * the emitted body — the SAME zero-test / `sub(&n, &1)` predecessor /
//!     one-self-call MIR contract R1 emits, at the `trust_bignum::Nat`
//!     carrier, from one shared emitter;
//!   * the F-LAYER gate (`check_faithful_wf_functional`): side A's spine
//!     re-parsed by the gate itself, side A's declaration closure audited
//!     EMPTY, side A's decrease proofs BORROWED into side B's sentinel slots,
//!     side B kernel-checked at side A's own functional type, its post-borrow
//!     closure audited, and only then kernel defeq of the two functionals.
//!
//! **WHY THE CLOSURE AUDIT IS PART OF THE ACCEPTANCE, not hygiene.** R2's
//! termination evidence is the kernel's typing rule at the decrease slot
//! (`rec : (y : Nat) → Nat.lt y x → Nat` — a non-decreasing self-call has no
//! proof to supply). Probe c1 measures, adversely, that ONE assumed decrease
//! switches that rule off: with `axiom bogus : ∀ x, Nat.lt (succ x) x` in
//! scope a DIVERGING functional kernel-checks and the definition ADMITS. So a
//! recursive `Faithful` is minted only over an audited-empty closure, and
//! `control_8_wf_rec_emitter_mutation.rs` runs that refusal through the whole
//! route.
//!
//! `-Z trust-verify=off` per the parity precedent: the mint, the emission and
//! the faithfulness gate must all run WITHOUT the verifier switched on — the
//! gate is not allowed to hide behind the switch. The verify-on boundary is
//! the sibling's job (`clean_origin_wf_rec_verify_on.rs`).
//!
//! SMALL INPUTS ON PURPOSE: the emitted self-call form recurses O(value)
//! deep — `countdownSum(2^64)` would be 2^64 frames — and each frame allocates
//! a bignum. That is a stated operational cost of the honest first rung, not a
//! soundness caveat; a loop/accumulator emission is an optimization-ladder
//! rung under §6f (same gate, different MIR), named future work.
//!
//! DELIBERATELY NOT HERE, and stated rather than blurred:
//!
//!   * **`gcd`.** Still not callable — but **CORRECTED 2026-08-25, and the
//!     correction reverses the attribution.** This paragraph used to say the
//!     block was `first-party/clean`'s (`RecursionOutsideFragment`, "no
//!     kernel-checked declaration to plan from"). Re-measured through the real
//!     session at the current pin (`r6_nat_mul_probes` q1): R3 (`27a46804e`)
//!     widened the signature and R4 (`1852198c0`) added the Bool-test
//!     spelling, so `def gcd (a b : Nat) : Nat := if h : 0 < b then
//!     gcd b (a % b) else a  termination_by b` ELABORATES, kernel-checks with
//!     a foundational-only axiom closure, and computes `gcd 12 18 = 6`. There
//!     IS a kernel-checked declaration; what refuses it is THIS compiler's
//!     single-parameter fix-spine reader (`check_wf_nat_signature` plus a
//!     `recognise_wf_nat_rec` written for the 5/6-argument spine and the
//!     `fun _ => Nat` motive — the two-parameter lowering threads the other
//!     parameter through an ARROW motive and binds a third lambda in the
//!     functional). A SUBTRACTIVE `gcd` is not a way around it: it decreases
//!     only in `a + b`, and a two-parameter MEASURE is refused island-side by
//!     name (q2).
//!   * **a decrease by more than one.** `f (n - 2)` is a legal, terminating,
//!     kernel-admitted definition (probe c6 gates one), but the emitted
//!     contract's predecessor is exactly `Nat::sub(&n, &1)`, so the planner
//!     refuses rather than emitting a body that decreases by one for a
//!     definition that decreases by two. `control_8`'s boundary row pins it.
//!   * **a cross-crate call.** `FaithfulnessMethod::WellFoundedFunctionalDefeq`
//!     has no wire tag, deliberately (the verdict rests on a borrow and a
//!     closure audit taken in the exporting crate's environment, and the wire
//!     unit carries no field for either), so exporting a certificate for this
//!     def refuses at the export seam. Same accounting as R1's per-equation
//!     verdicts. A wire spelling is its own reviewed format change.
//!
//! THE VALUES BELOW ARE PROBE-PINNED, not invented:
//! `r2_wf_equation_probes` w9 measured `countdownSum 0/1/3/5 ≡ 0/1/6/15` at
//! the kernel in BOTH numeral lanes, with `countdownSum 5 ≢ 14` as the
//! refuting control. What runs here is the EMITTED binary computing them.

extern crate trust_bignum;

clean {
    def countdownSum (n : Nat) : Nat := if h : 0 < n then n + countdownSum (n - 1) else 0
    termination_by n

    def keep2 (a : UInt64) (b : UInt64) : UInt64 := a
}

// CTFE: the u64-fragment const traverses `mir_for_ctfe`'s kernel-gated lane
// with the well-founded def present in the same island session. A `const`
// calling `countdownSum` itself is NOT claimed — the bignum runtime's
// operations are not `const fn`, so const-evaluating the recursive body fails
// with an ordinary const-eval error, and this increment states that boundary
// rather than papering over it.
const K: u64 = keep2(41, 7);

fn nat(value: u64) -> trust_bignum::Nat {
    trust_bignum::Nat::from_u64(value)
}

fn main() {
    // The triangular numbers `n + (n-1) + … + 1`, computed by the EMITTED
    // recursion. Every one of these is a w9 row.
    for (input, expected) in [(0u64, 0u64), (1, 1), (3, 6), (5, 15)] {
        let out = countdownSum(nat(input));
        assert_eq!(
            out.to_u64(),
            Some(expected),
            "countdownSum({input}) must compute {expected} through the emitted \
             well-founded recursion"
        );
    }

    // The base case, straight through the zero arm of the emitted zero test.
    let out = countdownSum(nat(0));
    assert_eq!(out.to_u64(), Some(0), "countdownSum(0) must take the zero arm");

    assert_eq!(K, 41, "the CTFE lane must serve the kernel-gated projection");
}
