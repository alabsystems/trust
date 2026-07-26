//@ battery-lane: B-lean
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=off --crate-type=lib
//! LANE B (Lean, `clean { … }` parser island, kernel authority) — real Lean.
//!
//! Definitions and theorems in the SECOND language, at item position. Grammar
//! vanilla Rust rejects, so no valid Rust program changes meaning (E10).
//!
//! Pinned to `-Ztrust-verify=off` deliberately: island parsing, elaboration
//! and KERNEL CHECKING are mandatory on every build regardless of the verify
//! flag — only Rust VC routing is disabled. So a pass here is evidence about
//! the KERNEL, uncontaminated by the solver lane. That is the property
//! `clean_island_grammar` pins and this battery re-exercises with a larger,
//! genuinely proof-carrying island.

clean {
    def Always (p : Nat -> Prop) : Prop := forall n, p n

    def Doubled (n : Nat) : Nat := Nat.add n n

    theorem always_unfolds (p : Nat -> Prop) : Always p = Always p := rfl

    theorem doubled_unfolds (n : Nat) : Doubled n = Nat.add n n := rfl

    theorem le_refl_nat : forall (n : Nat), Nat.le n n :=
        fun n => Nat.le.refl n

    theorem u64_le_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn rust_side_still_compiles(x: u64) -> u64 {
    x
}
