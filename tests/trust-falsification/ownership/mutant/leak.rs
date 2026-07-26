#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// MUTANT: `t` is never moved out — it is DROPPED at scope end (a leak Rust's
// type system permits). Trust must REJECT `#[trust::must_consume]` (build error),
// proving the linearity check is non-vacuous.
pub struct Token(u32);
#[trust::must_consume]
pub fn handle(t: Token) {
    let _ = t.0;
}
