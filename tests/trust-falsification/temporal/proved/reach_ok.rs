#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// SUPERIORITY (temporal / ty lane): `#[trust::reachable]` proves every enum
// state is reachable from the initial state via `step` (no dead state) — a
// reachability property rustc cannot express — by exhaustive model checking.
pub enum S { A, B, C }
#[trust::reachable]
pub fn step(s: S) -> S {
    match s { S::A => S::B, S::B => S::C, S::C => S::C }
}
