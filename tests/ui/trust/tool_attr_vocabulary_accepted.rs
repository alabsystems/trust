//@ needs-trust-verify
//@ check-pass
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ dont-check-compiler-stderr

//! **Every `trust::` attribute the compiler consumes must survive the sweep, and
//! must do so WITHOUT `#![register_tool(trust)]`.**
//!
//! Two independent things are pinned here.
//!
//! 1. **Tool registration.** `trust` is predefined, so none of the spellings
//!    below is `E0433: cannot find module or crate 'trust'`. Before that, an
//!    armed `#[trust::skip]` was a hard error in any crate that had not
//!    hand-written `#![feature(register_tool)] #![register_tool(trust)]`, which
//!    is why `ay-dpll`, `ay-encode` and `ay-sat` could not carry the vocabulary
//!    at all. This file deliberately does NOT write `register_tool`; if the
//!    predefined entry is removed, every attribute below becomes E0433 and this
//!    test fails loudly.
//!
//! 2. **The vocabulary is not too narrow.** The E5 conservation check in
//!    `rustc_resolve::macros::smart_resolve_macro_path` hard-errors on any
//!    `trust::<name>` outside `trust_types::trust_attr_namespace`'s
//!    consumer-derived table, so an over-tight table would break working code.
//!    Each name below is read by a live consumer, cited per row in that table:
//!    `item_has_trust_skip_attr` (`skip`), `item_has_trust_attr` (the six after
//!    it), `trait_panic_free::PANIC_FREE`, `panic_free_drop::PANIC_FREE_DROP`,
//!    and the pre-resolution loop-clause recognizer
//!    `ast::trust_contract::trust_loop_clause_attr_kind` (`loop_invariant`,
//!    `decreases`).
//!
//!    `panic_free_drop` and the loop-clause pair are the names a call-site-only
//!    enumeration misses — the first is matched inside its own module, the other
//!    two before name resolution — so they are the reason this file exists
//!    alongside the unit tests.
//!
//! Advisory policy is used so that the VERDICTS these attributes trigger — the
//! panic-freedom lanes and the temporal model checker in particular — report
//! instead of failing. What this file is about is the attribute vocabulary, not
//! whether any particular proof goes through, and pinning the latter here would
//! make an unrelated prover change look like a regression in this guard.

#[trust::skip]
pub fn skipped() {}

#[trust::assume_total]
pub fn assumed_total(x: u32) -> u32 {
    x
}

#[trust::backing]
pub struct Backing {
    ptr: *const u8,
    len: usize,
}

#[trust::must_consume]
pub struct MustConsume(pub u32);

#[trust::single_writer]
pub struct SingleWriter(pub u32);

#[trust::verified_codegen]
pub fn verified_codegen(x: u32) -> u32 {
    x
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum State {
    Start,
    Done,
}

#[trust::terminating]
#[trust::reachable]
pub fn step(s: State) -> State {
    match s {
        State::Start => State::Done,
        State::Done => State::Done,
    }
}

// `panic_free` is a TRAIT-METHOD-DEFINITION contract: it is declared once on the
// trait so every implementation inherits it at the point it is written. Measured
// on the stage2 built for this change, putting it on a free function is refused
// with "must be declared on a trait method DEFINITION" — a POSITION check the
// consumer owns, entirely separate from the namespace check under test here.
pub trait Steps {
    #[trust::panic_free]
    fn advance(&self, x: u32) -> u32;
    //~^ WARN is vacuous in this crate: 0 implementations
}

// `panic_free_drop` governs the drop glue of a `dyn Trait` object, so it is
// declared on a trait THIS crate owns — not on a `Drop` impl, which the consumer
// refuses by position for the same reason.
// It also discloses that it enforces NOTHING yet. That disclosure is pinned
// below rather than suppressed: `panic_free_drop` is a consumed name — it is
// matched by path and refused by position, which is what puts it in the
// vocabulary — and it is separately honest about charging no caller. Both facts
// are true at once and neither implies the other.
#[trust::panic_free_drop]
pub trait Held {
    //~^ WARN is recognized but NOT YET ENFORCED
    fn held(&self) -> u32;
}

// The loop-clause transport, in the STATEMENT position the recognizer accepts.
// These are consumed before name resolution, so they never reach the sweep —
// which is exactly what this case checks, because an item-only sweep would have
// left this position unswept while tool registration made it inert.
pub fn loop_clauses(mut n: u32) -> u32 {
    #[cfg_attr(trust_verify, trust::loop_invariant(n <= 100))]
    #[cfg_attr(trust_verify, trust::decreases(n))]
    while n > 0 {
        n -= 1;
    }
    n
}
