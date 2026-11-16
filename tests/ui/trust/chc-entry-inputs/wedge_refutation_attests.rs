//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ edition: 2024
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A `&mut` parameter's pointee leaf, read at its ENTRY value, is a function input,
//! so trust-mc's refutation of a postcondition over it may speak
//! (`typed_chc_entry_input_names`, `compiler/rustc_mir_transform/src/trust_verify.rs`).
//!
//! The acceptance pair is aterm's grid wedge, reduced
//! (`aterm:crates/aterm-grid/src/grid/scrollback_offload.rs`, `abort_reflow_offload`).
//! Before the change, the mutant's refutation was demoted to Unknown: the payload is
//! `¬¬self*.0.0` over the inputs `["_1", "self"]`, and `self*.0.0` had no definition.
//! A build without `-Ztrust-policy=advisory` failed on coverage, not on the bug.
//!
//! Every other function here is a case the new inputs must NOT turn into a false
//! `failed` row: each is either correct, or reads a leaf the rule refuses to ground.
//!
//! Each exit arm publishes its own postcondition row: in `abort_mutant` the
//! early-return arm — taken only when `detached` is already false — proves
//! (kernel-certified), while the fallthrough and whole-function rows still refute,
//! so its counts read `1 proved, 2 failed`; the mutant still does not prove.

pub struct Storage {
    pub detached: bool,
}

pub struct Window {
    pub storage: Storage,
}

impl Window {
    pub fn abort_fixed(&mut self)
    //~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown
        ensures !self.storage.detached
    {
        if !self.storage.detached {
            return;
        }
        self.storage.detached = false;
    }

    pub fn abort_mutant(&mut self)
    //~^ NOTE Trust verification: 1 proved, 2 failed, 0 unknown
        ensures !self.storage.detached
    {
        if !self.storage.detached {
            return;
        }
        // MUTANT: `self.storage.detached = false;` deleted.
    }

    // Correct: the callee resets the flag. The write happens behind a call, so the
    // exit value is a havoc with no definition, and the refutation (if any) must stay
    // demoted, never become a counterexample against a correct body.
    pub fn abort_via_callee(&mut self)
    //~^ NOTE Trust verification: 0 proved, 0 failed, 2 unknown
        ensures !self.storage.detached
    {
        reset(&mut self.storage);
    }

    // Correct: the reset goes through a local alias of the leaf. If vcgen did not
    // version that write, the exit read would be the bare ENTRY name and grounding it
    // would turn this correct body into a false counterexample.
    pub fn abort_via_alias(&mut self)
    //~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
        ensures !self.storage.detached
    {
        let flag = &mut self.storage.detached;
        *flag = false;
    }

    // Correct, with a loop: the body is cyclic, so the flattened-arm attestation
    // does not apply.
    pub fn abort_by_loop(&mut self)
    //~^ NOTE Trust verification: 0 proved, 0 failed, 2 unknown
        ensures !self.storage.detached
    {
        while self.storage.detached {
            self.storage.detached = false;
        }
    }
}

#[inline(never)]
pub fn reset(storage: &mut Storage) {
    storage.detached = false;
}

pub struct Small {
    pub n: u8,
}

// Correct for every value a caller can pass. Grounding `s*.0` is sound only if its
// sort is the u8's exact image (8-bit bit-vector); at an unbounded `Int` sort a model
// could pick 256, so the rule refuses to ground it.
pub fn keep_u8(s: &mut Small)
//~^ NOTE Trust verification: 0 proved, 0 failed, 2 unknown
    ensures s.n <= 255
{
    let _ = s;
}

// A by-value parameter in an `ensures` denotes its ENTRY value (D2,
// docs/design/2026-07-09-two-language-spec-surface.md §3), and the payload says so:
// `range(a) ∧ _0 == 5 ∧ ¬(a == 5)`. A caller passing `a = 0` violates the clause, so
// the refutation is real. vcgen fail-closes a clause over a REBOUND parameter to a
// bare `Not(post)` with the parameter free (`postcondition_references_mutated_param`);
// that placeholder never attests, because a rebound parameter is not an input of a
// postcondition payload (`typed_chc_rebound_parameters`, asking vcgen's own predicate
// `rebound_parameter_places`). This body does not reach it: no rebinding of `a` remains.
pub fn set_five(mut a: u32) -> u32
//~^ NOTE Trust verification: 0 proved, 2 failed, 0 unknown
    ensures a == 5
{
    a = 5;
    a
}

// A MUTANT through a SHARED reference: the refutation is real, but `&T` pointee
// leaves are not grounded (interior mutability can change them behind a call), so it
// stays demoted. This pins the rule's scope.
pub fn look_mutant(s: &Storage) -> bool
//~^ NOTE Trust verification: 0 proved, 0 failed, 2 unknown
    ensures result == !s.detached
{
    s.detached
}
