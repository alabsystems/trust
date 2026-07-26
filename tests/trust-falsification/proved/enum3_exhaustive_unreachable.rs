#![crate_type = "lib"]
// COMPLETENESS (`[unreach]`, fuzzer-revealed 2026-06-24): a 3-variant exhaustive
// `match` lowers to `SwitchInt(discriminant)` with cases {0,1,2} and an
// `otherwise → Unreachable` arm that is genuinely dead (a valid `E`'s discriminant
// is one of {0,1,2}). The TyCtxt extractor certifies this with
// `exhaustive_enum_unreachable`; `build_exhaustive_enum_validity_facts` conjoins
// the validity fact `disc ∈ {0,1,2}`, making the trap's violation formula
// `(disc ∉ {0,1,2}) ∧ (disc ∈ {0,1,2})` UNSAT by pure propositional resolution
// over opaque `Eq` atoms (`formula_is_unsat_by_exhaustive_discriminant`). Trust
// used to RUNTIME-CHECK this trap — ay finds the contradiction UNSAT but cannot
// STRICTLY reconstruct a trivial equality/Boolean contradiction (only
// linear-arithmetic UNSAT), so it stayed `[unreach] runtime-checked`. The
// structural discharge (`promote_structurally_dead_unreachable`) now PROVES it,
// at parity with the native trust-mc structural-reachability path. Genuinely
// panic-free, so this verifies (exit 0). The soundness twin — a NON-exhaustive
// trap — is `mutant/enum_partial_unreachable.rs`, which must still refute.
pub enum E {
    A,
    B,
    C,
}
pub fn classify(e: E) -> u32 {
    match e {
        E::A => 1,
        E::B => 2,
        E::C => 3,
    }
}
