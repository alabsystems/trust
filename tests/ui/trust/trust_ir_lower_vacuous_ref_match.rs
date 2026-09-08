//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-VRM): a match on a SHARED reference whose single unguarded arm
//! tests nothing and binds nothing is straight-line code — the lane emits no
//! dispatch at all, and does not lower the scrutinee (reading a shared
//! reference to a fieldless place can have no effect; rustc's own MIR for this
//! match is likewise a `goto`).
//!
//! `Match(ref scrutinee)` is a ROUTING gate, not a shape: its bodies have five
//! unrelated pointee shapes and four of them hand off to downstream owners that
//! are each independently architectural. This lane claims exactly the one that
//! is straight-line.

#[derive(PartialEq, Eq)]
pub struct S;

pub const C: &S = &S;

pub fn vacuous() -> u32 {
    match C {
        C => 11,
    }
}

fn main() {
    assert_eq!(vacuous(), 11);
}
