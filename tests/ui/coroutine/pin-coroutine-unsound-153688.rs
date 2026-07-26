// Regression test for rust-lang#153688: pin!() in coroutine/gen block unsound.
// Trust: Part of #860
//
// This test verifies that the pin!() macro's type constraint (from the fix for
// rust-lang#153438) correctly prevents deref coercions inside gen blocks and
// coroutine contexts. Without the fix, a type annotation on the result of pin!()
// inside a gen block could introduce a deref coercion that violates the pinning
// invariant.
//
// Gen blocks are movable coroutines (Iterator::next takes &mut self, not
// Pin<&mut Self>), so the coroutine can be moved between yields. If pin!()
// allowed a deref coercion, the resulting Pin would point to a location that
// is not actually pinned, enabling unsound behavior.

//@ edition: 2024

#![feature(gen_blocks)]

use std::pin::Pin;
use std::pin::pin;

struct Wrapper(u32);

impl std::ops::Deref for Wrapper {
    type Target = u32;
    fn deref(&self) -> &u32 {
        &self.0
    }
}

impl std::ops::DerefMut for Wrapper {
    fn deref_mut(&mut self) -> &mut u32 {
        &mut self.0
    }
}

fn main() {
    // Test 1: pin!() in a gen block must not allow deref coercions.
    // pin!(Wrapper(42)) should produce Pin<&mut Wrapper>, NOT Pin<&mut u32>.
    let _iter = gen {
        let _x: Pin<&mut u32> = pin!(Wrapper(42));
        //~^ ERROR mismatched types
        // [pending soundness check] ERROR mismatched types
        yield 1u32;
    };

    // Test 2: Same test in an async block (immovable coroutine).
    // The type constraint must work identically.
    let _fut = async {
        let _x: Pin<&mut u32> = pin!(Wrapper(42));
        //~^ ERROR mismatched types
        // [pending soundness check] ERROR mismatched types
    };

    // Test 3: pin!() with a reference type in a gen block.
    // pin!(&mut val) should produce Pin<&mut &mut u32>, NOT Pin<&mut u32>.
    let _iter2 = gen {
        let mut val: u32 = 42;
        let _x: Pin<&mut u32> = pin!(&mut val);
        //~^ ERROR mismatched types
        // [pending soundness check] ERROR mismatched types
        yield 1u32;
    };
}
