//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ dont-require-annotations: NOTE
//! A1 (design note `requires-hyps` revision 2, increment A) — P-A1.
//!
//! THE MEASURED DEFECT this fixture pins. `rmax_le_left` is true, it is
//! kernel-checked, and it is the theorem a working programmer writes: `rmax`
//! returns the larger of its two arguments, so `result <= a` holds exactly when
//! `b <= a` — which this function DECLARES as its precondition. Before A1 the
//! only goal the compiler could build for a cited `ensures` was the
//! UNCONDITIONAL one
//!
//!     ∀ a b, rmax a b ≤ a
//!
//! which is false (`rmax 0 5 = 5`), so the citation could not be written at all
//! and the author saw a raw kernel `TypeMismatch` dump with no indication that
//! the missing piece was the precondition (wf1 probe `66b`, both toolchains,
//! exit 1).
//!
//! WHAT THIS FIXTURE ASSERTS. The compiler now also builds
//!
//!     ∀ a b, (b ≤ a) → rmax a b ≤ a
//!
//! and tells the author, at the citation, that their theorem proves it. The
//! hypothesis is the elaboration of the QUERY-OWNED canonical proposition
//! callers are charged — not source text — and only the arithmetic-free
//! allow-list `E-allow` is eligible, because that is the fragment on which the
//! Clean reading and the charged reading provably agree.
//!
//! WHAT CHANGED WITH OR-A1 (ruled 2026-09-27, increment 1a): the build is now
//! GREEN. The hypothesis `Nat.le (UInt64.toNat b) (UInt64.toNat a)` is both the
//! Clean reading of `b <= a` and its lifted reading `(b as nat) <= (a as nat)`,
//! so the theorem proves `G1★` and the citation is creditable on the
//! kernel-canonical link — at `Trusted`, never `Certified`. The solver already
//! proved every postcondition row here, and a conditional credit never replaces
//! an existing proof, so the rows keep their own authority (MEASURED on stage 1,
//! 2026-09-28: the per-row counts are unchanged, 3 proved / 2 kernel-certified per
//! function); what changes is that the citation is VALID and no longer a hard
//! error.
//!
//! The Lean content below is MEASURED, not predicted: the identical island,
//! clause, precondition and theorem discharge on rung (2) in the crates-level
//! test `clean_island::tests::p_a1_a_case_split_proof_under_a_real_precondition_discharges`.
//! The stderr is measured on stage 1 (2026-09-28).

clean {
    theorem rmax_le_left : forall (a : UInt64) (b : UInt64),
        Nat.le (UInt64.toNat b) (UInt64.toNat a) ->
        Nat.le (UInt64.toNat (if a < b then b else a)) (UInt64.toNat a) :=
        fun a b h => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => a) (fun _ => b))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun _ => Nat.le.refl (UInt64.toNat a))
            (fun _ => h)
}

pub fn rmax(a: u64, b: u64) -> u64
    requires b <= a
    ensures result <= a by rmax_le_left
    //~^ NOTE kernel-discharges this postcondition UNDER this function's `requires`
    //~| NOTE these preconditions assumed: h0 = `b <= a` (`requires` #0)
    //~| NOTE requires-link: kernel-canonical
    //~| NOTE creditable to the postcondition obligation at `Trusted`
{
    if a < b { b } else { a }
}

/// POINTER-SIZED TWIN. The same clause on `usize` parameters.
///
/// It carries, and the fact that it does is a FIX, not a given. The candidate
/// derivation cross-checks the query-owned contract domain against the function
/// signature, and that check compares RUST spellings: the query publishes
/// `PointerSizedInt{64}`, whose Rust spelling is `usize`. Handed the DISCHARGE
/// binder table — which has already rewritten `usize` to `u64` for the target —
/// it compared `usize` against `u64`, disagreed, and dropped every pointer-sized
/// precondition on the floor with a message about two internal tables. The
/// cross-check now runs against the unresolved table it is documented against
/// (`trust_fn_param_type_names`) and only the RETURNED spelling is resolved, so
/// the two sides are compared after the same resolution every other E9 discharge
/// lane applies.
pub fn rmax_usize(a: usize, b: usize) -> usize
    requires b <= a
    ensures result <= a by rmax_le_left
    //~^ NOTE kernel-discharges this postcondition UNDER this function's `requires`
    //~| NOTE these preconditions assumed: h0 = `b <= a` (`requires` #0)
    //~| NOTE requires-link: kernel-canonical
{
    if a < b { b } else { a }
}

fn main() {}
