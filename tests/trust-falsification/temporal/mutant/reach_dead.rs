#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// MUTANT: variant C is never PRODUCED, so it is unreachable from A via step
// (a dead state). Trust must REJECT `#[trust::reachable]` (build error).
pub enum S { A, B, C }
#[trust::reachable]
pub fn step(s: S) -> S {
    // C is never PRODUCED — unreachable from A via step (dead state).
    match s { S::A => S::B, S::B => S::B, S::C => S::C }
}
