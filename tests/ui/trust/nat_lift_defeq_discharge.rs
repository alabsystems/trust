//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! nat-lift POSITIVE fixture: a `u64` Rust function discharges a postcondition
//! stated over a Lean definition written in **`Nat`** — the carrier every owner
//! model is already written in.
//!
//! Before this, the clause could not be stated at all: a clause atom has one
//! machine carrier and a call argument is never coerced, so naming a
//! `Nat`-parameter definition from a `u64` function was refused with "declares
//! parameter 0 at carrier `Nat`, but the argument is a `u64` term ... never
//! coerced". `e as nat` is the ratified explicit spelling (spec surface §12.3);
//! it lifts by the EXACT injection `UInt64.toNat`, and the goal
//!
//!     ∀ (u : UInt64), Eq Nat (UInt64.toNat (trust_import_…__first u))
//!                            (first_nat (UInt64.toNat u))
//!
//! closes by definitional equality — measured in
//! `crates/trust-certify/src/clean_island.rs::nat_lift_wire_tests` on the same
//! wire this fixture exercises.
//!
//! What this does NOT do: the lift is never inserted for you. An uncast machine
//! term at a `Nat` position is refused with the cast printed — the implicit
//! lift is owner ruling OR-1 and is not taken here.

clean {
    def first_nat (a : Nat) (b : Nat) : Nat := a
}

fn first(a: u64, b: u64) -> u64
    ensures (result as nat) == first_nat(a as nat, b as nat)
    //~^ NOTE island definition `first_nat` kernel-discharges this postcondition
{
    a
}

fn main() {
    let _ = first(3, 4);
}
