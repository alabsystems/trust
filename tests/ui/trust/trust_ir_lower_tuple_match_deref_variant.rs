//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-DPE): a tuple match whose elements are `&Enum` references
//! matched THROUGH the reference — `#[derive(PartialEq)]`'s
//! `match (self, other) { (E::A(a), E::A(b)) => *a == *b, .. }` — lowers by
//! loading the enum through each element pointer, testing its tag, and
//! binding each by-ref scalar payload field as a snapshot pointer. Under
//! `strict`: the derived `eq` bodies must lower, and so must the explicit
//! form below.

#[derive(PartialEq, Clone, Copy)]
pub enum E {
    A(u32),
    B(u8, u8),
    C,
}

fn same_a(x: &E, y: &E) -> bool {
    match (x, y) {
        (E::A(a), E::A(b)) => *a == *b,
        (E::B(p, _), E::B(q, _)) => *p == *q,
        _ => false,
    }
}

fn main() {
    if !(E::A(1) == E::A(1)) || E::A(1) == E::A(2) || E::B(1, 2) == E::C {
        std::process::exit(1);
    }
    if !same_a(&E::A(7), &E::A(7)) || same_a(&E::B(1, 2), &E::A(1)) {
        std::process::exit(2);
    }
}
