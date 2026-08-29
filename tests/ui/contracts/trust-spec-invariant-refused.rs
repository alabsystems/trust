//! Trust: `#[trust::invariant(..)]` must be REFUSED, not silently erased.
//!
//! THE BUG THIS LOCKS OUT. `trust-spec` exports an `invariant` passthrough proc
//! macro. Until the resolver gained a mapping for it, that passthrough RAN: the
//! attribute was deleted from the token stream and nothing downstream ever saw
//! it. MEASURED on toolchain `trust-e26541e3`, before the fix:
//!
//!   * a file with `#[trust::invariant(false)]` and the same file with the
//!     attribute removed produced a BIT-IDENTICAL obligation set (same ids,
//!     kinds and outcomes), and
//!   * `#[trust::invariant(this is not even an expression ~~~)]` compiled
//!     clean with exit code 0.
//!
//! An annotation that looks like a specification but contributes nothing is
//! worse than no annotation, because a reader — and the verification ratchet —
//! counts it as a guarantee.
//!
//! WHY A REFUSAL AND NOT A LOWERING. A function- or item-position `invariant`
//! has no defined program point. The genuine loop-invariant machinery is keyed
//! to `rustc_hir::LoopClause::loop_id`, the identity of the `while` expression
//! the clause belongs to; an attribute on an item has no loop to bind to. The
//! only other existing target, `VcKind::ContractInvariant`, is refuted as a bare
//! `Not(predicate)` with no program point at all — MEASURED, that makes it
//! PROVED exactly when the predicate is a TAUTOLOGY (`invariant(1 == 1)` reports
//! `outcome=proved` while the same function's real `overflow:add` obligation
//! stays `failed`). Lowering onto that would manufacture a proved row that
//! constrains nothing, which is strictly worse than erasing it.
//!
//! THIS FILE PINS THE VERIFY-ON LANE (`-Z trust-verify=on`), where the resolver
//! swaps the trust-spec proc macro for the compiler-owned `ExpandTrustInvariant`
//! builtin. Note the explicit compile-flag: compiletest runs the `ui` suite with
//! `-Z trust-verify=off` by default, and the swap is deliberately gated on
//! verification being enabled, so without that flag this file would exercise the
//! shim lane instead and the compiler diagnostic below would never fire.
//!
//! Companion tests: `trust-spec-invariant-refused-vanilla.rs` (the SAME source
//! shape with verification OFF — the refusal must survive there too, which is
//! the property that stops a build-mode choice from resurrecting the erasure),
//! `trust-spec-invariant-not-in-scope.rs` (E0433 without the crate),
//! `trust-spec-decreases-not-exported.rs` (E0433, must stay that way).
//@ compile-flags: -Z trust-verify=on
//@ proc-macro: trust.rs
//@ edition: 2021

#![allow(dead_code)]

// The plain spelling on a function.
#[trust::invariant(x > 0)]
//~^ ERROR `trust::invariant` is not a verified contract surface
fn annotated_fn(x: i32) -> i32 {
    x + 1
}

// ITEM POSITION. Before the fix this was accepted in TOTAL SILENCE, while the
// identical `#[trust::requires(..)]` on a struct was already a hard error
// ("contract annotations can only be used on functions"). That asymmetry is
// exactly how the erasure hid: the surface that verified nothing was also the
// surface that complained about nothing. This is the shape `trust-spec`'s own
// `tests/passthrough.rs` used to ship as documented usage.
#[trust::invariant(self.value >= 0)]
//~^ ERROR `trust::invariant` is not a verified contract surface
struct Counter {
    value: i32,
}

// A SYNTACTICALLY MEANINGLESS PAYLOAD. This compiled clean before the fix: the
// passthrough never looked at its argument, so there was nothing to reject. The
// refusal fires on the attribute itself, so it catches this too.
#[trust::invariant(this is not even an expression ~~~)]
//~^ ERROR `trust::invariant` is not a verified contract surface
fn garbage_payload(x: i32) -> i32 {
    x
}

// RENAME RESISTANCE. The refusal keys on the RESOLVED DEF, not on the literal
// `trust::invariant` spelling, so every alias reaches it. Keying on the
// spelling is the precise fail-open bug that was already paid for once with
// `requires`/`ensures` — see the post-mortem comment in
// `rustc_resolve::macros::trust_spec_contract_attr_extension`: every other
// spelling fell through to the passthrough, so the code compiled clean while
// the contract was silently never verified.
use trust::invariant;
use trust::invariant as renamed_invariant;

#[invariant(x > 0)]
//~^ ERROR `trust::invariant` is not a verified contract surface
fn via_bare_import(x: i32) -> i32 {
    x
}

#[renamed_invariant(x > 0)]
//~^ ERROR `trust::invariant` is not a verified contract surface
fn via_renamed_import(x: i32) -> i32 {
    x
}

#[::trust::invariant(x > 0)]
//~^ ERROR `trust::invariant` is not a verified contract surface
fn via_absolute_path(x: i32) -> i32 {
    x
}

// The two clauses that DO have exact semantics must keep working unchanged.
// This is the guard against a refusal that over-reaches: the fix the diagnostic
// recommends has to actually compile.
#[trust::requires(x > 0)]
#[trust::ensures(move |r: &i32| *r > 0)]
fn still_supported(x: i32) -> i32 {
    x
}

fn main() {}
