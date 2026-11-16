//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ dont-require-annotations: NOTE
//! A1 — N-A4, THE VACUITY GUARD.
//!
//! `requires a < a` admits no input. The conditional goal
//! `∀ a b, a < a → rmax a b ≤ a` is therefore TRUE, and `vacuous_le` proves it
//! by eliminating the impossible hypothesis. The kernel is right to certify it.
//!
//! This is not a soundness failure — nothing false is proved — but it is a
//! green that lies: a note saying "your postcondition is discharged under
//! `requires`" would read as "this contract is enforced", when the row
//! constrains no reachable call at all. A precondition can be vacuous by
//! contradiction (`a < a`) or by leaving its own carrier (`c.degree > 255` on a
//! `u8` field), and both are ordinary authoring mistakes.
//!
//! So the positive note is WITHHELD and a different one is emitted, naming the
//! cause. The search runs over the exact carriers the contract query published,
//! which is what makes the `u8` case detectable at all; it is a bounded
//! enumeration, so a negative result withholds a claim and never asserts one
//! about the program.
//!
//! The citation stays a HARD ERROR, and since the OR-A1 review (round 2) the
//! error names this cause — the withheld conditional discharge — instead of
//! falling through to the typed statement check, which reported a kernel
//! `TypeMismatch` against the UNCONDITIONAL goal: a mismatch the author did not
//! make.
//!
//! MEASURED at crates level: `clean_island::tests::
//! n_a4_a_contradictory_precondition_discharges_anything` pins that the kernel
//! DOES discharge this goal — i.e. that the guard, not the kernel, is what stops
//! the misleading note. The compiletest DIRECTIVES and annotations here are
//! predicted — bless required.

clean {
    theorem vacuous_le : forall (a : UInt64) (b : UInt64),
        Nat.lt (UInt64.toNat a) (UInt64.toNat a) ->
        Nat.le (UInt64.toNat (if a < b then b else a)) (UInt64.toNat a) :=
        fun a b h => False.elim (Nat.lt_irrefl (UInt64.toNat a) h)
}

pub fn rmax_vacuous(a: u64, b: u64) -> u64
//~^ ERROR Trust strict verification failed for
//~| WARN is not assumed for body verification: no satisfiable witness found for the predicate
    requires a < a
    ensures result <= a by vacuous_le
    //~^ NOTE proves this postcondition only under preconditions for which no satisfying input was found
    //~| NOTE the search is a bounded enumeration, so this is "none found", not a proof that the preconditions are contradictory
    //~| ERROR and that conditional discharge was withheld: the bounded search found no input satisfying the carried preconditions
{
    if a < b { b } else { a }
}

fn main() {}
