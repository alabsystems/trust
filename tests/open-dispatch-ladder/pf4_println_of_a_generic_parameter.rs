//@ trust-ladder: refuses
//@ trust-ladder-crate-type: bin
//! GUARD RAIL. `T` is a type PARAMETER, so no impl resolves and there is no
//! body to establish. Any rewiring that reads a verdict must fail closed here.
use core::fmt::Debug;
pub fn show<T: Debug>(x: T) { println!("{:?}", x); }
fn main() { show(1u32); }
