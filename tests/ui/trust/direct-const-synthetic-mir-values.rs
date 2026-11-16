//@ run-pass
//@ edition: 2021
//@ compile-flags: -Zvalidate-mir -Ztrust-verify=off

// Direct consts have no HIR body. Their synthetic MIR must still preserve
// values through free, inherent and trait-associated projections, beside an
// ordinary const. This is a runtime value check, not a proof-coverage claim.
#![feature(gca_min_const_items)]

use std::gca;

const DIRECT: u8 = gca!(7u8);
const ORDINARY: u8 = 3;

struct S;

trait HasValue {
    #[rustc_always_gca]
    const VALUE: u8;
}

impl HasValue for S {
    const VALUE: u8 = gca!(9u8);
}

impl S {
    const INHERENT: u8 = gca!(5u8);
}

fn read() -> u8 {
    DIRECT + ORDINARY + S::INHERENT + <S as HasValue>::VALUE
}

fn main() {
    assert_eq!(read(), 24);
}
