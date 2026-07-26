//@ compile-flags: -Z trust-verify=off
//! An authored clause with no predicate is a hard error (design §1.2-6:
//! authored specs fail as type errors — refusing the claimed contract, never
//! accepting it silently).

pub fn missing_predicate(x: u32) -> u32
    requires
{
    //~^ ERROR expected a predicate expression after the contract clause keyword
    x
}

fn main() {
    let _ = missing_predicate(1);
}
