//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The OTHER half of §13.1, and the half that would otherwise stay open: a
//! literal the predicate language cannot carry must be REFUSED BY NAME.
//!
//! Widening the grammar closes the four spellings that were measured. It closes
//! nothing about the next one. Before this change the refusal was
//! `TrustContractPredicateKind::Unsupported` and nothing else — the clause was
//! accepted, no error was emitted, the proof did not happen, and the only
//! symptom was an UNKNOWN row naming the whole predicate. Standing ruling v7/D3
//! says a refusal must carry the fix, with options; this fixture is what holds
//! the compiler to it.
//!
//! `-Ztrust-policy=advisory` is deliberate. Under the default policy the
//! unproved clauses ALSO produce the strict-lane errors, which would let this
//! fixture pass on those alone and say nothing about the message. Advisory
//! downgrades those to warnings, so the only errors left are the ones this
//! fixture is actually about.
//!
//! `300u8` leads because it is the case where silence would be UNSOUND rather
//! than merely unhelpful: rustc rejects that literal in a body, but a native
//! clause is a parser island that is never type-checked as Rust, so reading it
//! as the bound `result <= 300` over a `u8` result would state a bound every
//! `u8` satisfies — a vacuous clause wearing a proved row's clothes.
//!
//! Two spellings are deliberately ABSENT because rustc's own lexer reaches them
//! first, which is the correct layering and worth recording so nobody adds them
//! here and finds a different message: `0x` is `E0768: no valid digits found
//! for number`, and `0b2` is "invalid digit for a base 2 literal".

pub fn suffix_out_of_range(x: u8) -> u8 ensures result <= 300u8 { x }
//~^ ERROR unsupported numeric literal `300u8` in this `ensures` clause

pub fn signed_suffix_out_of_range(x: i8) -> i8 ensures result <= 129i8 { x }
//~^ ERROR unsupported numeric literal `129i8` in this `ensures` clause

pub fn not_a_suffix(x: u32) -> u32 ensures result <= 123abc { x }
//~^ ERROR unsupported numeric literal `123abc` in this `ensures` clause

/// Rust's radix prefixes are lower-case only, so `0X1` is an unknown suffix and
/// not a hexadecimal one. Reading it as hex would be inventing a dialect.
pub fn upper_case_radix_prefix(x: u32) -> u32 ensures result <= 0X1 { x }
//~^ ERROR unsupported numeric literal `0X1` in this `ensures` clause

pub fn beyond_the_carrier(x: u32) -> u32 ensures result <= 999999999999999999999999999999999999999999 { x }
//~^ ERROR unsupported numeric literal `999999999999999999999999999999999999999999`

/// The neighbouring spelling that a grammar widening makes newly plausible. It
/// is refused, and it says so — closing only the integer half would leave this
/// exactly as invisible as the separator used to be.
pub fn float_literal(x: u32) -> u32 ensures result <= 1.5 { x }
//~^ ERROR unsupported numeric literal `1.5` in this `ensures` clause

/// A `requires` reaches the same reader down a different road: its refusal is
/// routed through `SpecParseError::UnsupportedIntegerLiteral` in
/// `trust-types`, not through the compiler's snippet lane. Naming it here pins
/// BOTH consumers of the one grammar, which is the whole reason the grammar
/// lives in one module.
pub fn precondition_literal(x: u32) -> u32 requires x <= 300u8 { x }
//~^ ERROR invalid `requires` clause
