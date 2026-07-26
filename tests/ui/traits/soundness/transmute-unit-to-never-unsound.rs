//@ known-bug: #126529
//@ check-pass
// Trust: regression test for rust-lang#127555
// Part of #859
//
// The compiler unsoundly accepts a transmute from `()` (unit / zero-sized
// type with one value) to `!` (never type / zero-sized type with NO values).
// Since `!` is uninhabited, any value of type `!` can be used to produce
// a value of any type via `match val {}`. Transmuting `()` to `!` therefore
// allows constructing arbitrary values in safe code (via the never type's
// exhaustive match).
//
// The root cause is that `transmute` checks that source and destination
// have the same size (both are zero-sized), but does not check
// inhabitedness. A ZST-to-ZST transmute should be rejected when the
// destination is uninhabited.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/127555
//
// STATUS: Uses `std::convert::Infallible` (stable equivalent of !) to
// demonstrate the pattern without requiring nightly. When fixed, the
// compiler should reject transmute from () to any uninhabited ZST.

#![allow(unreachable_code, invalid_value)]

use std::convert::Infallible;

fn unit_to_uninhabited() -> Infallible {
    // Both () and Infallible are zero-sized, so transmute accepts this.
    // But Infallible has no valid values, so this is instant UB.
    unsafe { std::mem::transmute::<(), Infallible>(()) }
}

// Once we have a value of an uninhabited type, we can produce any type.
fn make_any<T>() -> T {
    // Infallible can be matched exhaustively with no arms (it has no
    // variants). But we actually reach this code — the transmute above
    // gives us a "value" of type Infallible, which is UB.
    match unit_to_uninhabited() {}
}

fn main() {
    // If the transmute is accepted, this produces a String from nothing.
    // This is unsound: it reads uninitialized/garbage memory as a String.
    let _s: String = make_any();
    // Don't actually use _s — just verify the code compiles.
    // The fact that it compiles at all is the bug.
}
