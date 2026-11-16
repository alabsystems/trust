//@ trust-ladder: refuses
//@ trust-ladder-row: core::hash::Hash>::hash
//! THE SAME RULE, A DIFFERENT OFFENDING TYPE. `derive(Hash)` is refused on
//! `<u32 as core::hash::Hash>::hash::<__H>` — the open generic parameter
//! `H: Hasher`, not a `Formatter` and not a trait object. It is here so that a
//! fix aimed at `Formatter` cannot be mistaken for a fix of the class: this row
//! must stay red until the locality gate itself moves.
#[derive(Hash)]
pub struct S { pub a: u32 }
