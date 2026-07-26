#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// SUPERIORITY (temporal / ty lane): rustc cannot reason about whether a state
// machine TERMINATES. Trust extracts the enum-step transition machine from MIR
// and PROVES convergence (no livelock) by exhaustive finite-state model checking.
// Idle -> Running -> Done (a fixed point): every state reaches a fixed point.
pub enum State { Idle, Running, Done }
#[trust::terminating]
pub fn step(s: State) -> State {
    match s {
        State::Idle => State::Running,
        State::Running => State::Done,
        State::Done => State::Done,
    }
}
