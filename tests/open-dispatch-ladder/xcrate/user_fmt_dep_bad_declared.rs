//@ trust-ladder-xcrate: refuses
//@ trust-ladder-xcrate-dep: libdbad
//@ trust-ladder-xcrate-declare: libdbad
//! GUARD RAIL for D4-A: declaring a dependency buys re-derivation, not trust.
//! Its panicking `Debug` impl is found panicking here. Going green is a FALSE
//! PROOF until shown otherwise.
extern crate libdbad;
fn main() { println!("{:?}", libdbad::D); }
