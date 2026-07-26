#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// MUTANT: `a` is consumed but `b` is DROPPED (leaked). Trust must REJECT
// `#[trust::must_consume]` — proving it checks EVERY owned parameter, not just one.
pub struct Token(u32);
fn sink(_t: Token) {}
#[trust::must_consume]
pub fn handle(a: Token, b: Token) { sink(a); let _ = b.0; }
