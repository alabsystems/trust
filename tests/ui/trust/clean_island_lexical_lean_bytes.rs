//@ compile-flags: -Z trust-verify=off
//@ check-pass
//! Every byte a Lean file may contain is opaque to the island's boundary,
//! and none of it reaches the Rust lexer: `--` and nested `/- -/` comments
//! holding quotes and braces, strings with escaped quotes and braces, raw
//! strings, char literals `'{'` `'}'` `'\''`, `«…»` names, identifier
//! primes, and nested `{ … }` structure instances. Only a structural `}`
//! closes the island (`rustc_parse::lexer::trust_clean_island`). Before, a
//! `"` inside a Lean comment opened a RUST string literal that swallowed the
//! rest of the file, and a `}` inside a comment closed the island early —
//! the two `clean_island_lexical_*_comment` fixtures used to pin exactly
//! that failure as a limit.

clean {
    -- a line comment: it's got a "quote and a } brace
    /- a block comment " } /- nested } -/ still the outer one -/
    /-- a doc comment with a } -/
    structure P where
      x : UInt64
      y : UInt64
    def origin : P := { x := 0, y := 0 }
    def shifted : P := { origin with x := 1 }
    def «odd } name» : Nat := 1
    def brace_char : Char := '{'
    def close_char : Char := '}'
    def quote_char : Char := '\''
    def s1 : String := "a\"}b{"
    def raw1 : String := r"x}y"
    def raw2 : String := r#"a"b}"#
    def h' (a : UInt64) : UInt64 := a
    theorem h'_eq (h' : 0 = 0) : 0 = 0 := h'
    def after : Nat := 2
}

fn main() {}
