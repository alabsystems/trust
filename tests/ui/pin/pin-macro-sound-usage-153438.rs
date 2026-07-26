// Regression test for rust-lang#153438: pin!() sound usages still work.
// Trust: Part of #860
//
// The fix for #153438 must not break legitimate pin!() usage.
// This test verifies that normal pinning, and safe CoerceUnsized on the
// *result* of pin!() (which is safe because it doesn't move the value),
// continue to work.

//@ check-pass

use std::pin::Pin;
use std::pin::pin;
use std::marker::PhantomPinned;

trait MyTrait {}

struct MyStruct {
    _pinned: PhantomPinned,
}

impl MyTrait for MyStruct {}

fn takes_pin_ref(_: Pin<&mut dyn MyTrait>) {}

fn main() {
    // Basic pinning works
    let x = pin!(42u32);
    let _: Pin<&mut u32> = x;

    // Pinning a !Unpin type works
    let _y = pin!(MyStruct { _pinned: PhantomPinned });

    // CoerceUnsized on the Pin result is safe and should work.
    // This coercion happens AFTER the Pin is constructed, so it doesn't
    // move the underlying value — it only adjusts the fat pointer metadata.
    let z = pin!(MyStruct { _pinned: PhantomPinned });
    takes_pin_ref(z);
}
