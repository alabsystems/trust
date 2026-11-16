//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-require-annotations: NOTE
//! B0 (design note `requires-hyps` revision 2 §3.7) — the diagnostic half of
//! increment B, which needs no owner ruling and changes no verdict.
//!
//! `ident_isl` is a real, kernel-checked Clean island definition of this crate,
//! visible three lines above the clause that names it. Calling it from an
//! `ensures` works (the kernel judges the postcondition against this function's
//! imported defining equation). Calling it from a `requires` does not, because
//! a native clause payload is validated against the CLOSED source-contract
//! predicate vocabulary, of which no island definition — and no Rust function —
//! is a member.
//!
//! Before B0 the author was told only
//!
//!     error: invalid `requires` clause: unsupported source-contract call `ident_isl`
//!
//! whose natural reading is "the compiler cannot see my island". It can: what is
//! missing is the LANE for this clause role, and the two sides of a signature
//! are not governed by the same admission rule. The headline is unchanged; the
//! notes now say which of the two it is, and what to do instead (v7/D3).
//!
//! Increment B1 — unfolding an arithmetic-free Bool island predicate into the
//! clause grammar under a kernel-checked schematic equivalence — is NOT built
//! here: it needs owner ruling OR-B1 (island identity vs the hierarchical shared
//! symbol graph) and a measurement of the schematic bridge. Until then this
//! clause stays refused, which is the fail-closed direction.
//!
//! The compiletest DIRECTIVES and annotations are predicted — bless required.
//! The battery counterpart is `tests/two-language-battery/lane-c-combo/
//! c4_island_in_requires.rs`, which stays `battery-expect: frontier`.

clean {
    def ident_isl (x : UInt64) : UInt64 := x
}

/// CONTROL — the same island definition, the same call, on the ENSURES side.
/// Its presence is what makes the rejection below attributable to the clause
/// ROLE rather than to the island, the definition, or the call.
pub fn pass_through(x: u64) -> u64
    ensures result == ident_isl(x)
{
    x
}

pub fn guarded(x: u64) -> u64
    requires ident_isl(x) == x
    //~^ ERROR invalid `requires` clause: unsupported source-contract call `ident_isl`
    //~| NOTE is a Clean island definition in this crate, not an unknown name
    //~| NOTE `ensures` is the one clause role with an island lane today
    //~| HELP state the predicate in the clause grammar
{
    x
}

fn main() {}
