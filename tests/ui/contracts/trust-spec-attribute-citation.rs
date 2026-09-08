//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ proc-macro: trust.rs
//@ edition: 2021
//@ check-pass
//@ dont-require-annotations: NOTE
//! Trust E9 — a `by <thm>` CITATION on the ATTRIBUTE contract surface.
//!
//! The first-class signature surface (`fn f(..) ensures P by T { .. }`) is a
//! grammar vanilla Rust rejects, so any file that uses it is trustc-only. That
//! confined every citation in the veripb client to a hand-maintained twin file
//! excluded from its stock build: not one contract sat on code the program
//! actually runs.
//!
//! `#[trust::ensures(..)]` is an ordinary attribute, so it IS `cfg_attr`-
//! gateable and CAN sit on a real function in a crate that must still build
//! with stock cargo. Until this landed it had no citation handling at all: the
//! `by T` suffix was swallowed into the opaque payload span, the clause text
//! became `result <= x by self_le`, and the predicate degraded to
//! `Unsupported` with NO citation recorded anywhere. A silently dropped
//! citation is the dangerous failure — the contract reads as checked while
//! nothing checked it.
//!
//! ONE CITATION REPRESENTATION, TWO SURFACES: a cited attribute payload is
//! parsed by the SAME `parse_trust_native_clause` the signature surface uses
//! and stored in the SAME native lane, so from the AST onwards the two
//! spellings below are indistinguishable and share one discharge path.

clean {
    theorem self_le : forall (x : UInt64), Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

// The signature surface — the lane that already worked, kept here as the
// control the attribute lane must match exactly.
pub fn keep_native(x: u64) -> u64
    ensures result <= x by self_le
{
    x
}

// The attribute surface. Same clause, same theorem, same kernel discharge.
#[trust::ensures(result <= x by self_le)]
pub fn keep_attribute(x: u64) -> u64 {
    x
}

// THE PAYOFF SPELLING: `cfg_attr`-gated, so the same source is plain Rust
// under stock rustc. `trust_verify` is a COMPILER-PROVIDED cfg — set exactly
// when verification is active, never settable with `--cfg` — so no flag is
// needed here and none is available to a stock build.
// `trust-spec-attribute-citation-cfg-attr.rs` is the paired stock-semantics
// half (verification off, attribute stripped).
#[cfg_attr(trust_verify, trust::ensures(result <= x by self_le))]
pub fn keep_gated(x: u64) -> u64 {
    x
}

fn main() {}
