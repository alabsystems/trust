//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-SP): a STRUCT payload destructure in an enum match —
//! `E::V(P { x, y })`, `E::V(W(v))`. wave-NP's shape minus the refutability: the
//! outer arm's Switch case already commits the variant, and a struct destructure
//! adds no second discriminant test, so it records BINDS only — no entry-block
//! test, no fallthrough edge — and therefore composes with an exhaustive default
//! (the popped arm keeps its variant index and extracts identically). Two plain
//! `ExtractField`s per bind: the payload struct out of the enum aggregate (slot
//! `1 + field`), then the scalar-or-float field out of the struct.
//!
//! NEGATIVE CONTROL, the reason this is a pin: a nested VARIANT inside the
//! struct (`M::H(Holder { l: L::A(v) })`) is refutable — it would owe a test
//! this lane deliberately does not mint — and must stay refused
//! (`EnumMatch(struct payload subpattern not a binding)`).

pub struct Point {
    pub x: f64,
    pub y: f64,
}
pub enum Shape {
    Rectangle(Point, Point),
    Circle(Point, f64),
}
// The issue-3753 shape: struct payloads on both arms, exhaustive (no `_`), so
// the last arm is popped as the default WITH its struct binds carried.
pub fn area(s: Shape) -> f64 {
    match s {
        Shape::Rectangle(Point { x, y }, Point { x: x2, y: y2 }) => (x2 - x) * (y2 - y),
        Shape::Circle(_, r) => r * r,
    }
}
pub struct Wrap(pub i32);
pub enum K {
    Value(Wrap),
    Other,
}
// The tuple-struct spelling (`W(v)` is a Leaf subpattern too).
pub fn hello(k: K) -> i32 {
    match k {
        K::Value(Wrap(v)) => v,
        K::Other => 0,
    }
}
// NEGATIVE CONTROL: a refutable subpattern inside the struct stays refused.
pub enum L {
    A(i32),
    B,
}
pub struct Holder {
    pub l: L,
}
pub enum M {
    H(Holder),
    N,
}
pub fn neg_nested(m: M) -> i32 {
    match m {
        M::H(Holder { l: L::A(v) }) => v,
        _ => 0,
    }
}
pub fn main() {}
