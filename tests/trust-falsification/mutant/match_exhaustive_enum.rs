#![crate_type = "lib"]
// MUTANT of proved/match_exhaustive_enum.rs: the `None` arm panics, and `None`
// IS reachable (the caller may pass it). The verifier MUST refuse this (exit 1) —
// the panic-freedom obligation fails with a verified counterexample. This guards
// the `Unreachable`-as-obligation lane: making an exhaustive match's otherwise
// arm a *provable* infeasibility obligation must never let a genuinely reachable
// panic slip through as proved.
pub fn match_exhaustive_enum(o: Option<i32>) -> i32 {
    match o {
        Some(v) => v,
        None => panic!("none"),
    }
}
