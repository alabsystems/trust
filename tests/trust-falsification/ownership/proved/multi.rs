#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// SUPERIORITY (multi-parameter ownership linearity): BOTH owned parameters must
// be consumed. Trust checks each owned (ADT) parameter independently via the move
// dataflow; here both are moved into `sink`, so it PROVES must-consume.
pub struct Token(u32);
fn sink(_t: Token) {}
#[trust::must_consume]
pub fn handle(a: Token, b: Token) { sink(a); sink(b); }
