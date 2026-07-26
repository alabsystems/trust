//@ compile-flags: -Z trust-verify=off
//@ check-fail

// A quote is a prime only when immediately adjacent to its identifier.
// Whitespace must preserve vanilla Rust's unterminated-character diagnostic.
fn main() {
    let x = 0;
    let _ = stringify!(x '); //~ ERROR unterminated character literal
}
