//@ trust-ladder: verifies
//! CONTROL. `format!` writes into a `String`, not a caller-supplied writer.
pub fn f() -> String { format!("{}", 1u32) }
