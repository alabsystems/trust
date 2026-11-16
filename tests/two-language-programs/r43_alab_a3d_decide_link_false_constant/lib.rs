//! NEGATIVE TWIN of `r42`: the guard's MAGIC CONSTANT is wrong, and the link
//! must refuse it.
//!
//! The island below is `r42`'s, character for character. ONE token in the Rust
//! changes — `depth < 21` becomes `depth < 22` — and with it the two decisions
//! stop being equivalent: depth 21 is admitted by the body and refused by
//! `span_fits_isl` (`3 * 22 = 66`, which does not fit a 64-bit shift).
//!
//! THIS IS THE WHOLE POINT OF THE ROW ABOVE. a3d's existing contract
//! (`ensures result == depth_fits_isl(depth)`, an uncited defeq clause) does
//! NOT catch this: it would be satisfied by moving the 21 in the Lean model to
//! match, at which point the Rust and the Lean agree with each other and both
//! are wrong. The cited clause is stated over the ARITHMETIC, which cannot be
//! moved, so a wrong cutoff has nowhere to hide.
//!
//! Only the CITED function is present. `octree_depth_guard` is left out on
//! purpose: with a mutated body its uncited clause fails too, and a row that
//! refuses for two reasons cannot attribute its refusal to either.
//!
//! MEASURED 2026-09-20 on `trustc 1.99.0-dev (379912412 2026-09-19)`, through
//! this row's own lane (`trustc --crate-type lib lib.rs`): exit 1,
//! `0 proved, 0 failed, 2 unknown out of 2 obligation(s)`, and
//!
//! ```text
//! error: citation `depth_fits_is_span_fits` failed the strict Clean
//!        statement/certification audit: strict certification audit failed:
//!        [TermRejected { error: "TypeMismatch { expected: Pi(… Bool …
//!        Pi(… UInt32 … Eq Bool (BVar 1) (span_fits_isl (BVar 0)))), inferred:
//!        Pi(… UInt32 … Eq Bool (Decidable.decide (LT.lt (BVar 0)
//!        (UInt32.ofNat 21)) …) (span_fits_isl (BVar 0)))" }]
//! error: Trust strict verification failed for `lib::octree_depth_fits`
//! ```
//!
//! THE MUTATION CONTROL, measured in the same session through the same command:
//! this exact file with `22` put back to `21` exits 0 with
//! `2 proved, 0 failed, 0 unknown` and no `error:` line. One token is the whole
//! difference, so the refusal is attributable to the constant and to nothing
//! else.
//!
//! TWO THINGS A READER SHOULD TAKE FROM THAT MESSAGE, both measured:
//!
//!   1. It is FAIL-CLOSED but not informative. The `expected` type it prints
//!      quantifies over `result` (`Pi Bool …`) rather than binding `result` to
//!      the body, so it is a statement no theorem could prove — the refusal is
//!      correct and strictly stronger than the real goal, but the text does not
//!      say "your body's constant does not match the theorem you cited". The
//!      whole `Expr` is rendered with Rust's `{:?}`, which is not a v7/D3
//!      diagnostic. Fixing that is a trust-side diagnostics item; it is NOT
//!      fixed here, and this row pins the refusal, not the wording.
//!   2. The maintained `trustc-audit-refused` lane now requires an ordinary
//!      exit 1, this citation's strict statement-audit diagnostic, a kernel
//!      `TypeMismatch`, and the strict refusal for `lib::octree_depth_fits`.
//!      Crashes and unrelated syntax or loader errors cannot pass. This pins
//!      an audit refusal, not a counterexample or a proved false proposition;
//!      the historical wire above reports unknown obligations. Read it beside
//!      `r42`, whose arithmetic is the same and whose cutoff is correct.

clean {
    theorem decide_eq_decide_mpr (p : Prop) (q : Prop)
        (dp : Decidable p) (dq : Decidable q) (h : Iff p q) :
        Eq (Decidable.decide p dp) (Decidable.decide q dq) :=
      Decidable.casesOn
        (motive := fun i => Eq (Decidable.decide p i) (Decidable.decide q dq)) dp
        (fun hnp =>
          Decidable.casesOn
            (motive := fun j => Eq Bool.false (Decidable.decide q j)) dq
            (fun _ => Eq.refl Bool.false)
            (fun hq => False.elim (hnp (Iff.mpr h hq))))
        (fun hp =>
          Decidable.casesOn
            (motive := fun j => Eq Bool.true (Decidable.decide q j)) dq
            (fun hnq => False.elim (hnq (Iff.mp h hp)))
            (fun _ => Eq.refl Bool.true))

    def span_fits_isl (d : UInt32) : Bool :=
      Decidable.decide (Nat.lt (Nat.mul 3 (Nat.add (UInt32.toNat d) 1)) 64)
                       (Nat.decLt (Nat.mul 3 (Nat.add (UInt32.toNat d) 1)) 64)

    theorem depth_carrier_iff (d : UInt32) :
        Iff (LT.lt d (UInt32.ofNat 21)) (Nat.lt (UInt32.toNat d) 21) :=
      Iff.intro (fun h => h) (fun h => h)

    theorem span_fwd (n : Nat) (h : Nat.lt n 21) :
        Nat.lt (Nat.mul 3 (Nat.add n 1)) 64 :=
      Nat.lt_of_le_of_lt (Nat.mul 3 (Nat.add n 1)) 63 64
        (Nat.mul_le_mul_left (Nat.add n 1) 21 3 h)
        (by decide)

    theorem span_bwd (n : Nat) (h : Nat.lt (Nat.mul 3 (Nat.add n 1)) 64) :
        Nat.lt n 21 :=
      Or.casesOn
        (motive := fun _ => Nat.lt n 21)
        (Nat.le_or_lt n 20)
        (fun hle20 => Nat.succ_le_succ hle20)
        (fun hge21 =>
          False.elim
            (Nat.lt_irrefl 66
              (Nat.lt_of_le_of_lt 66 (Nat.mul 3 (Nat.add n 1)) 66
                (Nat.mul_le_mul_left 22 (Nat.add n 1) 3 (Nat.succ_le_succ hge21))
                (Nat.lt_of_le_of_lt (Nat.mul 3 (Nat.add n 1)) 64 66
                  (Nat.le_of_lt h) (by decide)))))

    theorem depth_fits_is_span_fits : forall (d : UInt32),
        Eq (Decidable.decide (LT.lt d (UInt32.ofNat 21))
                             (instDecidableUInt32Lt d (UInt32.ofNat 21)))
           (span_fits_isl d) :=
      fun d =>
        decide_eq_decide_mpr
          (LT.lt d (UInt32.ofNat 21))
          (Nat.lt (Nat.mul 3 (Nat.add (UInt32.toNat d) 1)) 64)
          (instDecidableUInt32Lt d (UInt32.ofNat 21))
          (Nat.decLt (Nat.mul 3 (Nat.add (UInt32.toNat d) 1)) 64)
          (Iff.intro
            (fun h => span_fwd (UInt32.toNat d) (Iff.mp (depth_carrier_iff d) h))
            (fun h => Iff.mpr (depth_carrier_iff d) (span_bwd (UInt32.toNat d) h)))
}

/// THE MUTATION: `21` -> `22`. Everything else is `r42`'s.
pub fn octree_depth_fits(depth: u32) -> bool
    ensures result == span_fits_isl(depth) by depth_fits_is_span_fits
{
    depth < 22
}
