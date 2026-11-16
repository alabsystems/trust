//@ trust-ladder-xcrate: refuses
//@ trust-ladder-xcrate-dep: libderr
//@ trust-ladder-xcrate-declare: libderr
//! GUARD RAIL for D4-A: a re-derived dependency impl that is panic-free but
//! returns `Err(fmt::Error)` makes `println!` panic in std. Error transparency
//! (D1 increment 0) must refuse it. Going green is a FALSE PROOF.
extern crate libderr;
fn main() { println!("{:?}", libderr::D); }
