//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! THE NEGATIVE CONTROL for `contract_literal_spellings_prove`. Teaching the
//! predicate tokenizer to read `999_999_999` widens what it can PARSE; it must
//! not widen one atom of what it ACCEPTS AS TRUE. This repo has shipped the
//! opposite three times in fifteen days — a clause that quietly stops being
//! checked while the verdict stays green — so the pair is mandatory, not tidy.
//!
//! The shape is `ensures result == <literal>` over a pinned return, which is
//! the one equality form that discharges (§13.2). Each literal appears TWICE
//! over the same clause: once above a body that satisfies it and once above a
//! body that does not, with the false body chosen to be exactly what a
//! MISREADING of that spelling would make true —
//!
//!   `1_0`        -> `1`    (a parser that stopped at the separator)
//!   `0x3B9AC9FF` -> `0`    (a parser that stopped at the `x`)
//!   `0b111`      -> `111`  (a parser that ignored the radix)
//!   `1000u32`    -> `100`  (a parser that mangled the suffix)
//!
//! so "the clause parses" and "the clause denotes the right integer" cannot be
//! confused for one another. The `_wrong_` functions are annotated as errors:
//! each must be REFUSED. The `_right_` functions carry no annotation at all, so
//! the fixture also fails if the spelling regresses to unparseable — that would
//! emit an error compiletest was not told to expect.

pub fn separator_right() -> u32 ensures result == 1_0 { 10 }

pub fn separator_wrong() -> u32 ensures result == 1_0 { 1 }
//~^ ERROR verification

pub fn hex_right() -> u32 ensures result == 0x3B9AC9FF { 999999999 }

pub fn hex_wrong() -> u32 ensures result == 0x3B9AC9FF { 0 }
//~^ ERROR verification

pub fn binary_right() -> u32 ensures result == 0b111 { 7 }

pub fn binary_wrong() -> u32 ensures result == 0b111 { 111 }
//~^ ERROR verification

pub fn suffix_right() -> u32 ensures result == 1000u32 { 1000 }

pub fn suffix_wrong() -> u32 ensures result == 1000u32 { 100 }
//~^ ERROR verification
