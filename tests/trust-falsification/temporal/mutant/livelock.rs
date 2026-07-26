#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// MUTANT: A <-> B is a 2-cycle — the machine NEVER reaches a fixed point
// (livelock). Trust must REJECT the `#[trust::terminating]` assertion (build
// error), proving the temporal check is non-vacuous.
pub enum State { A, B }
#[trust::terminating]
pub fn step(s: State) -> State {
    match s {
        State::A => State::B,
        State::B => State::A,
    }
}
