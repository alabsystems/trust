//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! E6 — a projection off a `&mut` receiver is ACCEPTED BY THE GRAMMAR and then
//! NOT ASSUMED, loudly.
//!
//! This is the "what if the field is behind a reference that could be mutated"
//! question, and the answer is deliberately split across two components, so
//! this file pins the seam rather than either half.
//!
//! The compiler-query side that resolves `c.k` walks `ty::Ref(_, inner, _)`,
//! which matches `&T` and `&mut T` alike: it is a LAYOUT walk, and the layout
//! is the same. So the clause is admitted and the caller obligation is minted
//! and demanded, exactly as for a shared reference.
//!
//! The callee-side ASSUMPTION is where mutability decides. `&mut` pointee
//! derefs are not in `contract_assumption_gate`'s `shared_ref_params` — a `&T`
//! pointee cannot change for the reference's lifetime, so a caller-proved entry
//! fact holds at every body read, and a `&mut` pointee can — so
//! `assumable_param_base` refuses `c*.0` and the whole precondition set is
//! dropped with a named warning:
//!
//! ```text
//!   warning: `#[trust::requires]` on `exclusive` is not assumed for body
//!            verification: predicate references `c*.0`, which is not a parameter
//! ```
//!
//! DROPPING AN ASSUMPTION CAN ONLY WEAKEN A VERDICT (`contract_assumption_gate`
//! documents this as its invariant), so the `divzero` below stays REFUTED and
//! the build fails. That is the fail-closed direction: the feature does not
//! quietly become a `&mut` entry-state assumption that a body write could
//! stale. `shared` is the control on the same file — identical text, shared
//! receiver, and it proves.
//!
//! If a future change makes `&mut` field preconditions assumable, this file goes
//! GREEN, which is the signal to check that a real freshness argument came with
//! it — `exclusive_then_write` writes the very field the clause names.

pub struct Cfg {
    pub k: usize,
    pub n: usize,
}

// CONTROL: shared receiver, assumption admitted, division discharged.
pub fn shared(c: &Cfg) -> usize
    requires c.k != 0
{
    c.n / c.k
}

// `&mut` receiver: clause admitted, assumption DROPPED, division refuted.
pub fn exclusive(c: &mut Cfg) -> usize
    //~^ WARN `#[trust::requires]` on `exclusive` is not assumed for body verification: predicate references `c*.0`, which is not a parameter
    //~| ERROR Trust strict verification failed for `e6_requires_field_projection_mut_receiver_not_assumed::exclusive`
    requires c.k != 0
{
    c.n / c.k
}

// The body WRITES the field the clause names — the shape a stale entry fact
// would have to survive.
pub fn exclusive_then_write(c: &mut Cfg) -> usize
    //~^ WARN `#[trust::requires]` on `exclusive_then_write` is not assumed for body verification: predicate references `c*.0`, which is not a parameter
    //~| ERROR Trust strict verification failed for `e6_requires_field_projection_mut_receiver_not_assumed::exclusive_then_write`
    requires c.k != 0
{
    c.k = 0;
    c.n / c.k
}
