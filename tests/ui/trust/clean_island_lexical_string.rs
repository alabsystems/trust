//@ compile-flags: -Z trust-verify=off
//@ check-pass
//! Rust token trees keep a brace inside a quoted string opaque, so this part
//! of the documented Rust-tokenizable Clean subset remains supported.

clean {
    def brace_text : String := "}"
}

fn main() {}
