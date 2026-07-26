// Regression test for rust-lang#153438: pin!() prevents deref coercions (part 2).
// Trust: Part of #860
//
// This tests another vector of the same bug: using a wrapper type with DerefMut
// to smuggle a deref coercion into pin!().
//
// Without the type constraint fix, `pin!(wrapper)` with a type annotation
// `Pin<&mut Inner>` would apply wrapper's DerefMut to get &mut Inner, creating
// a Pin to a location that is NOT actually pinned (it's behind the Deref, not
// the local variable).
//
// With the fix, pin!(wrapper) always returns Pin<&mut Wrapper>, regardless of
// the expected type annotation.

use std::pin::Pin;
use std::pin::pin;
use std::ops::DerefMut;

struct Wrapper(u32);

impl std::ops::Deref for Wrapper {
    type Target = u32;
    fn deref(&self) -> &u32 {
        &self.0
    }
}

impl DerefMut for Wrapper {
    fn deref_mut(&mut self) -> &mut u32 {
        &mut self.0
    }
}

fn main() {
    // This must be rejected: pin!(Wrapper(42)) returns Pin<&mut Wrapper>,
    // not Pin<&mut u32>. A deref coercion cannot apply.
    let _x: Pin<&mut u32> = pin!(Wrapper(42));
    //~^ ERROR mismatched types
    // [pending soundness check] ERROR mismatched types
}
