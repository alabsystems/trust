//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! The soundness twin of println_runtime_value_run_pass.rs. A runtime value
//! whose Display is a foundational-TCB type (i32, str) may ride the
//! bundled-std-member completeness-gap tolerance; a value formatted through a
//! USER Display may NOT, because that impl can panic and its panic edge is not
//! an obligation of this caller (the formatter is reached through the absent std
//! print backend, and the bundled S::fmt panic obligations are erased by the
//! ROOT-scope inventory reset). The positive Display discriminator
//! function_format_args_all_foundational_display keeps main fatal, and the
//! annotation above pins THAT error, distinct from the incidental S::fmt one.
//!
//! S::fmt here divides by zero for S(1), so the program genuinely panics at
//! runtime; a tolerated verdict would be a false PROVE of a panicking program.
//! A DERIVED Display/Debug is treated identically (also a user impl).
use std::fmt;
struct S(i32);
impl fmt::Display for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", 100i32 / (self.0 - 1))
    }
}
fn main() {
    //~^ ERROR a value is formatted through a user
    let v = std::hint::black_box(1i32);
    println!("{}", S(v));
}
