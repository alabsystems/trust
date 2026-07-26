// Trust: Regression test for rust-lang#155333
// Attributes with missing tokens should not ICE
//@ check-pass

#[cfg_attr(all(), allow(unused))]
fn foo() {}

fn main() { foo(); }
