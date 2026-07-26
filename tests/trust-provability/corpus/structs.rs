//! Structs and enums — the shapes almost every crate defines.
pub struct Point { pub x: i32, pub y: i32 }
impl Point {
    pub fn new(x: i32, y: i32) -> Self { Point { x, y } }
    pub fn manhattan(&self) -> i32 { self.x.abs() + self.y.abs() }
    pub fn shift(&mut self, dx: i32) { self.x = self.x.wrapping_add(dx); }
}
pub enum State { Idle, Running(u32), Done { code: i32 } }
pub fn state_code(s: &State) -> i32 {
    match s { State::Idle => 0, State::Running(n) => *n as i32, State::Done { code } => *code }
}
