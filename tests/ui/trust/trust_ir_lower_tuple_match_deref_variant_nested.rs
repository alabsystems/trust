//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-DPE2): the payload snapshot of a `&Enum` tuple-match element
//! admits what the shared-borrow snapshot admits — here a NESTED enum
//! payload — so `#[derive(PartialEq)]` on an enum wrapping another derived
//! enum lowers end to end (the nested `eq` is a local body linked by the
//! seam). Under `strict`.

#[derive(PartialEq, Clone, Copy)]
pub enum Inner {
    A(u32),
    B,
}

#[derive(PartialEq, Clone, Copy)]
pub enum Outer {
    X(Inner),
    Y(u8),
}

fn main() {
    if !(Outer::X(Inner::A(1)) == Outer::X(Inner::A(1))) {
        std::process::exit(1);
    }
    if Outer::X(Inner::B) == Outer::Y(0) {
        std::process::exit(2);
    }
}
