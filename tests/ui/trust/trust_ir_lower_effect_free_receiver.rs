//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-EFR): the discarded `Fn*::call*` receiver allow-list gains two
//! PURE spellings — a non-union field read of a pure base, and a capturing
//! closure literal whose capture operands are themselves effect-free.
//!
//! On the havoc `ClosureCall { capturing: false }` path the receiver is
//! DISCARDED (a fresh unit-slot env replaces it), so the only obligation is
//! that evaluating it has no observable effects. `self.0` is a pure place
//! projection — exactly as discardable as the bare `VarRef` the list already
//! admits — and `(|| self.foo())()` constructs its env from borrows of pure
//! places only.
//!
//! `run-pass` is the point: every accepted body still computes through the
//! real program (the lane is NotRun on the differential — `contains_call` —
//! and never flips), so a wrong admission surfaces as a wrong VALUE here.
//!
//! `effectful_receiver_declines` is the fence: `.take()` mutates through
//! `&mut self` and `.unwrap()` can panic — discarding either would be
//! unsound, and the tag must stay.

/// Shape A: field-read receiver of a generic callee — `(self.0)(x)`.
pub struct W<F>(F);
impl<F: FnOnce(i32) -> i32> W<F> {
    pub fn go(self, x: i32) -> i32 {
        (self.0)(x)
    }
}

/// Shape C: a capturing closure literal receiver whose sole capture operand is
/// a borrow of a pure place (`self`).
pub trait Tr {
    fn foo(&self) -> i32;
    fn bar(&self) -> i32 {
        (|| self.foo())()
    }
}
struct T9;
impl Tr for T9 {
    fn foo(&self) -> i32 {
        7
    }
}

/// The fence: an effectful receiver (`.take().unwrap()`) keeps the refusal.
pub fn effectful_receiver_declines(mut o: Option<fn(i32) -> i32>, x: i32) -> i32 {
    (o.take().unwrap())(x)
}

fn main() {
    assert_eq!(W(|v| v + 1).go(4), 5);
    assert_eq!(T9.bar(), 7);
    assert_eq!(effectful_receiver_declines(Some(|v| v * 2), 3), 6);
}
