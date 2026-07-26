//@ known-bug: #152607
//@ check-pass
// Trust: Regression test for rust-lang#152607
// Check that associated type bounds from supertrait constraints are enforced
// on trait object types. Previously, `dyn Sub<Assoc = String>` was accepted
// even though `String: Copy` was required by the supertrait bound, enabling
// use-after-free on stable Rust.
//
// The key distinction from check-trait-object-bounds-{1..6} is that those
// tests catch the error through a function call with a trait bound (e.g.,
// `f::<dyn X<Y = str>>()` where `f` requires `T: X`). This test checks
// that the error is caught at the point where the dyn type is formed,
// even without an intermediary function imposing the bound.

trait Super {
    type Assoc;
}

// The `Assoc: Copy` bound comes from the supertrait clause, not from
// Super's definition of Assoc. This is the case that was unchecked.
trait Sub: Super<Assoc: Copy> {}

// String does not implement Copy — this must be rejected.
fn takes_sub(_: &dyn Sub<Assoc = String>) {}
// [pending soundness check] ERROR the trait bound `String: Copy` is not satisfied

// Valid usage: i32 implements Copy.
trait SafeSub: Super<Assoc: Copy> {}
fn takes_safe(_: &dyn SafeSub<Assoc = i32>) {}

fn main() {}
