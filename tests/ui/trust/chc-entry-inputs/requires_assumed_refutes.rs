//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ edition: 2024
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A postcondition of a function whose authored `requires` the assumption gate KEPT as a
//! body hypothesis attests again (`trust_mir_extract::contract_preconditions_all_assumed`,
//! read by `annotate_trust_mc_typed_chc_encoding_fidelity`). Its counterexample satisfies
//! the precondition, so it is a call the function can receive. A dropped `requires` still
//! declines: `tests/ui/trust/e9_requires_hypothesis_vacuous.rs` stays Unknown.
//!
//! Each exit arm publishes its own postcondition row: in `abort_mutant` the early-return
//! arm — under the assumed `generation > 0`, taken only when `detached` is already
//! false — proves (kernel-certified), while the fallthrough and whole-function rows
//! still refute, so its counts read `1 proved, 3 failed` (plus the assumed requires);
//! the mutant still does not prove.

pub fn clamp_fixed(x: u32) -> u32
//~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
    requires x < 100
    ensures result < 100
{
    x
}

// MUTANT: a real counterexample exists inside the precondition (x = 50).
pub fn clamp_mutant(x: u32) -> u32
//~^ NOTE Trust verification: 0 proved, 2 failed, 0 unknown
    requires x < 100
    ensures result < 10
{
    x
}

pub struct Storage {
    pub detached: bool,
}

// The grid wedge's mutant with an assumed precondition beside it.
pub fn abort_mutant(s: &mut Storage, generation: u32)
//~^ NOTE Trust verification: 1 proved, 3 failed, 0 unknown
    requires generation > 0
    ensures !s'.detached
{
    if generation == 0 || !s.detached {
        return;
    }
    // MUTANT: `s.detached = false;` deleted.
}
