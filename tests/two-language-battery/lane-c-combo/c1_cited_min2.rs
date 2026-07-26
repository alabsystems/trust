//@ battery-lane: C-combo
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on -Copt-level=0
//! LANE C (THE COMBO — one program, two languages) — cited discharge.
//!
//! This is the thesis of the whole design in one file: a REAL Rust program,
//! executable, whose postconditions are proven by THEOREMS WRITTEN IN LEAN in
//! the same source file, kernel-checked at compile time, with no solver proof
//! for those clauses.
//!
//! `pick_min` is ordinary Rust anyone would write. Its contract is discharged
//! by `min2_le_left`, a Lean theorem proved by genuine case analysis — not by
//! `rfl` and not by an axiom.
//!
//! PORTED 2026-07-25 to the `ite` encoding. The theorem's statement used to be
//! written over the compiler's internal encoding of the body:
//!
//!     Nat.le (UInt64.toNat (Bool.rec (fun _ => UInt64) y x
//!         (Bool.not (Nat.ble (UInt64.toNat y) (UInt64.toNat x))))) (UInt64.toNat x)
//!
//! It now reads `if x < y then x else y`, and the case split is on the
//! `Decidable` instance rather than on a manufactured comparison bool. The
//! helper lemma `min2_case` is gone: the split happens inline, so the island
//! dropped from 16 lines to 8. That readability gain is the same change that
//! makes `c6_readable_select.rs` work without any helper at all.

clean {
    theorem min2_le_left : forall (x : UInt64) (y : UInt64),
        Nat.le (UInt64.toNat (if x < y then x else y)) (UInt64.toNat x) :=
        fun x y => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt x y)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => y) (fun _ => x))) (UInt64.toNat x))
            (instDecidableUInt64Lt x y)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat x) (UInt64.toNat y)) h)
            (fun h => Nat.le.refl (UInt64.toNat x))

    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

/// Ordinary Rust. The Lean theorem above is its proof.
pub fn min2(a: u64, b: u64) -> u64 { if a < b { a } else { b } }

/// The combo: a Rust postcondition discharged by a Lean case-split proof.
pub fn pick_min(x: u64, y: u64) -> u64 ensures min2(x, y) <= x by min2_le_left { min2(x, y) }

/// A second mode: the result bound to the defining equation.
pub fn keep(x: u64) -> u64 ensures result >= x by u64_ge_refl { x }

fn main() {
    let (a, b) = (41u64, 7u64);
    let _outputs = (pick_min(a, b), keep(a));
}
