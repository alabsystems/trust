//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ check-pass
//! THE OTHER HALF OF THE BOUNDARY: what the tightened `to_string` stamp still
//! admits.
//!
//! `to_string_stamp_reference_peel_stays_closed.rs` and
//! `to_string_stamp_impersonated_string_refuted.rs` show the stamp REFUSING. A
//! refusal-only pair would pass just as well if the model had been deleted, and
//! deleting it is exactly the failure mode the tightening must not become. This
//! file is therefore the control: every `Self` below is a `SpecToString`
//! specialization read in `library/alloc/src/string.rs` in this tree, and each
//! must still be PROVED under `-Ztrust-policy=certify`, where an unproved
//! obligation is an error.
//!
//!   * `str` and the `to_string_str!` reference chain — `{ let s: &str = self;
//!     String::from(s) }`.
//!   * bare `String` — the same body.
//!   * bare `bool` — `String::from(if *self { "true" } else { "false" })`.
//!   * bare `char` — `encode_utf8` into a `char::MAX_LEN_UTF8` buffer, exactly
//!     the encoder's worst case.
//!   * bare `u32`/`i64` — `impl_to_string!`'s fixed `MAX.ilog10() + 1` digit
//!     buffer.

pub fn from_literal() -> String {
    "the quick brown fox".to_string()
}

pub fn from_str_param(s: &str) -> String {
    s.to_string()
}

/// Two references over `str` — inside `to_string_str!`'s twelve.
pub fn from_str_chain(s: &&str) -> String {
    ToString::to_string(&s)
}

pub fn from_string(s: String) -> String {
    s.to_string()
}

pub fn from_bool(b: bool) -> String {
    b.to_string()
}

pub fn from_char(c: char) -> String {
    c.to_string()
}

pub fn from_u32(n: u32) -> String {
    n.to_string()
}

pub fn from_i64(n: i64) -> String {
    n.to_string()
}
