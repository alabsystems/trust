//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **R1 ACCEPTANCE — STRUCTURAL RECURSION IS EMITTABLE AND CALLABLE.**
//! (§6e AS AMENDED + §6f,
//! `docs/design/2026-08-04-two-language-compiler-architecture.md`.)
//!
//! The island below is BYTE-CLASS-IDENTICAL to the `tozero` that
//! `recursion_boundary_probes.rs` measured ADMITTED by the island elaborator
//! (its value IS `fun n => @Nat.rec.{1} (fun _ => Nat) (OfNat.ofNat Nat 0 …)
//! (fun n ih => ih) n`) and REFUSED by the planner — probe r3's pin, flipped
//! EXPLICITLY in the change that landed the R1 lane. Nothing about the
//! declaration changed; the compiler grew:
//!
//!   * the `StructuralNatRec` plan/recognise arms (side A read into the
//!     closed `RecBodyExpr` vocabulary; termination evidence = the
//!     recursor-headed `FullKernelCheck` value, the kernel's own);
//!   * the emitted body: `is_zero` zero-test `SwitchInt`, `sub(&n, &1)`
//!     predecessor, ONE recursive `Call` against the def's own `DefId`, at
//!     the `trust_bignum::Nat` carrier;
//!   * the per-defining-equation gate (`check_faithful_equations`):
//!     per-minor-premise defeq with the recursive result held ABSTRACT, the
//!     kernel-checked recursive-argument identity, and equation-set
//!     completeness read from the kernel's own minor-premise count — the
//!     §6e IMPLEMENTATION AMENDMENT's judgment, never the vacuous
//!     constant-citing spelling (probe s2 is the permanent record of why).
//!
//! `-Z trust-verify=off` per the parity precedent: the mint, the emission and
//! the faithfulness gate must all run WITHOUT the verifier switched on — the
//! gate is not allowed to hide behind the switch. The verify-on boundary is
//! the sibling's job (`clean_origin_structural_rec_verify_on.rs`).
//!
//! SMALL INPUTS ON PURPOSE: the emitted self-call form recurses O(value)
//! deep — `tozero(2^64)` would be 2^64 frames. That is a stated operational
//! cost of the honest first rung, not a soundness caveat; a loop/accumulator
//! emission is an optimization-ladder rung under §6f (same gate, different
//! MIR), named future work.
//!
//! THIS FIXTURE IS ALSO A MEASUREMENT (RISK-6): a self-recursive
//! `optimized_mir` on a HIR-less def is the case the inliner's cycle
//! machinery (`mir_callgraph_cyclic`) exists for, and its behaviour on a def
//! with no HIR was unmeasured when the emitter landed. If this fixture ICEs
//! in the inliner, the recorded fallback is excluding Clean-origin defs from
//! inlining candidacy — a performance cost, never a correctness one.
//!
//! WHAT THE CONST BELOW DOES AND DOES NOT PIN: `K` traverses the CTFE lane
//! (`mir_for_ctfe` serves kernel-gated bodies) for a u64-fragment def
//! declared in the SAME island as the recursive def — pinning that the R1
//! arm coexists with the const lane. A `const` calling `tozero` itself is
//! NOT claimed: the bignum runtime's operations are not `const fn`, so
//! const-evaluating the recursive body fails with an ordinary const-eval
//! error (the RISK-8 accounting), and this increment states that boundary
//! rather than papering over it.
//!
//! DELIBERATELY NOT HERE: `fib`. Its user equations are measured
//! rfl-checkable against the `.cov`-backed constant (r1_equation_probes e4
//! — `fib 10 ≡ 55` computes at the kernel), but the `.cov` auxiliary's
//! result type `Prod Nat Nat` has no total Rust carrier in this toolchain
//! yet, so the emitter arm waits on the pair carrier.
//! `control_7_structural_rec_emitter_mutation.rs` pins both refusals
//! honestly (`fib`: NotEmittable; `fib.cov`: NoTotalCarrier); a fixture
//! asserting `fib(10) == 55` lands in the increment that lands the carrier.

extern crate trust_bignum;

clean {
    def tozero : Nat -> Nat
      | 0 => 0
      | n + 1 => tozero n

    def keep2 (a : UInt64) (b : UInt64) : UInt64 := a
}

// CTFE: the u64-fragment const traverses `mir_for_ctfe`'s kernel-gated lane
// with the recursive def present in the same island session.
const K: u64 = keep2(41, 7);

fn main() {
    // tozero(3) == 0 — the closed value the probes pinned at the kernel
    // (`r1_equation_probes` e5: `tozero 3 ≡ 0`, both numeral lanes) now
    // computed by the EMITTED binary.
    let out = tozero(trust_bignum::Nat::from_u64(3));
    assert_eq!(out.to_u64(), Some(0), "tozero(3) must compute 0 through the emitted recursion");

    // The base case, straight through the zero arm.
    let out = tozero(trust_bignum::Nat::from_u64(0));
    assert_eq!(out.to_u64(), Some(0), "tozero(0) must take the zero arm");

    assert_eq!(K, 41, "the CTFE lane must serve the kernel-gated projection");
}
