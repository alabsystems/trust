//@ compile-flags: -Z trust-verify=off
//@ check-fail
//! Lean nested block-comment delimiters are not Rust comments. A brace inside
//! one must fail closed until the lexer has a dedicated opaque-island mode.

clean {
    theorem before : 0 = 0 := rfl
    /- outer /- nested } -/ outer -/
    theorem after : 0 = 0 := rfl
} //~ ERROR unexpected closing delimiter: `}`

fn main() {}
