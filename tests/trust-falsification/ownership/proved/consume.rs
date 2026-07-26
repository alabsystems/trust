#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// SUPERIORITY (ownership / trust-vc lane): Rust's AFFINE types allow an owned
// value to be silently DROPPED. `#[trust::must_consume]` asserts LINEARITY — the
// owned parameter must be MOVED OUT (consumed) on every path, never dropped.
// Here `t` is moved into `sink`, so Trust PROVES it (sound move dataflow).
pub struct Token(u32);
fn sink(_t: Token) {}
#[trust::must_consume]
pub fn handle(t: Token) {
    sink(t);
}
