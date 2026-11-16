//@ fn-ptr-witness: verifies
//! THE ONE SHAPE WHERE THE GREEN IS EARNED, since 2026-09-19. `f` is provably
//! `g`: the MIR is `_1 = g as fn() (ReifyFnPointer)` then `copy _1()`, so the
//! target is statically known and `g` is verified as its own root like any other
//! function. `indirect_callee_is_a_reified_constant` recognises exactly that
//! shape — one assignment to the operand's local, a `ReifyFnPointer` cast of a
//! CONSTANT, no projection, no borrow — and every other shape in this directory
//! falls outside it and refuses.
//!
//! Before that carve-out this row was green for the WRONG reason (the call was
//! simply unmodelled, like f1/f2/f4), and it is kept as the boundary between the
//! two kinds of green.
fn g() {}
pub fn call() { let f: fn() = g; f(); }
