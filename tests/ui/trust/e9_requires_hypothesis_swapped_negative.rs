//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ dont-require-annotations: NOTE
//! A1 — N-A2, THE CLOSE NEGATIVE TWIN of `e9_requires_hypothesis_note.rs`.
//!
//! Byte-for-byte the same island, the same theorem, the same clause. ONE thing
//! differs: the precondition is `a <= b`, not `b <= a`.
//!
//! `rmax_le_left` needs `b <= a`. This function does not declare it and
//! therefore does not charge callers for it, so handing the theorem that
//! hypothesis would be a FALSE ACCEPT — the postcondition would be "proved"
//! from an assumption nobody ever establishes. `a = 0, b = 5` satisfies this
//! function's declared precondition and returns `5`, refuting `result <= a`.
//!
//! The hypothesis carried is the elaboration of THIS function's own `requires`,
//! so the conditional goal is `∀ a b, (a ≤ b) → rmax a b ≤ a`, which the cited
//! theorem does not state. Neither rung matches, nothing is discharged, and the
//! conditional-discharge note from the positive twin must NOT appear.
//!
//! MEASURED (not predicted) as the swapped arm of the crates-level test
//! `clean_island::tests::p_a1_a_case_split_proof_under_a_real_precondition_discharges`,
//! which asserts exactly this refusal. The compiletest DIRECTIVES are predicted
//! — bless required.

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

pub fn rmax_swapped(a: u64, b: u64) -> u64
//~^ ERROR Trust strict verification failed for
    requires a <= b
    ensures result <= a by rmax_le_left
    //~^ NOTE a SECOND goal was also tried for `rmax_le_left`
    //~| NOTE the cited theorem states neither goal
    //~| ERROR failed the strict Clean statement/certification audit
{
    if a < b { b } else { a }
}

fn main() {}
