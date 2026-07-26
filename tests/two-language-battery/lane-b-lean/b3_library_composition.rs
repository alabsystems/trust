//@ battery-lane: B-lean
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=off --crate-type=lib
//! LANE B (Lean) — proofs COMPOSED FROM THE KERNEL'S OWN LIBRARY.
//!
//! `b1` proves things by `rfl` and reflexivity, which exercises the island
//! pipeline but not the mathematics. This file composes real library lemmas
//! (`Nat.le_add_right`, `Nat.le_trans`) into new theorems, which is what
//! "Trust compiles pure Lean" has to mean if it means anything.
//!
//! It also probes a convention the battery needs pinned: this kernel's
//! fixtures pass lemma arguments EXPLICITLY
//! (`Nat.le_of_ble_eq_true (UInt64.toNat y) (UInt64.toNat x) h`), so these
//! theorems do the same. If the convention differs, the failure names the
//! constant and the battery has measured something worth knowing.

clean {
    def Doubled (n : Nat) : Nat := Nat.add n n

    theorem doubled_unfolds (n : Nat) : Eq Nat (Doubled n) (Nat.add n n) := rfl

    theorem le_doubled : forall (n : Nat), Nat.le n (Doubled n) :=
        fun n => Nat.le_add_right n n

    theorem le_doubled_trans : forall (n : Nat),
        Nat.le n (Doubled (Doubled n)) :=
        fun n => Nat.le_trans n (Doubled n) (Doubled (Doubled n))
            (Nat.le_add_right n n)
            (Nat.le_add_right (Doubled n) (Doubled n))
}

pub fn rust_side(x: u64) -> u64 {
    x
}
