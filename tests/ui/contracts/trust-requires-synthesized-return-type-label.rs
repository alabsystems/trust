//@ compile-flags: -Zcontract-checks=yes
// Trust: `parse_contract_requires_payload` pins a `#[requires]` checker closure
// to `-> bool`. That return type is synthesized, so a non-bool precondition's
// E0308 must not name it as "the return type" the expectation came from: one
// label, exactly as upstream (tests/ui/contracts/empty-requires.rs and the two
// `requires-*` siblings pin the unit case against pristine upstream output;
// `non_bool` pins a non-unit type). `user_written` is the control: a return
// type the USER wrote inside a contract is real and keeps its label.
#![expect(incomplete_features)]
#![feature(contracts)]

extern crate core;
use core::contracts::requires;

#[requires(1u32)]
//~^ ERROR mismatched types [E0308]
fn non_bool(x: u32) -> u32 {
    x
}

#[requires(let check = || -> bool { () }; check())]
//~^ ERROR mismatched types [E0308]
fn user_written(x: u32) -> u32 {
    x
}

fn main() {
    non_bool(1);
    user_written(1);
}
