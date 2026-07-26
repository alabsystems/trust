// Regression test for rust-lang#153688: pin!() sound usage in gen/async blocks.
// Trust: Part of #860
//
// This test verifies that legitimate uses of pin!() inside gen blocks and
// coroutine contexts continue to work after the fix for #153688. The fix
// must not reject valid patterns.
//
// Valid patterns include:
// - pin!() where the result is used within the same yield-free scope
// - pin!() in async blocks (which are immovable, so Pin is always valid)
// - pin!() where the type annotation matches the actual type

//@ check-pass
//@ edition: 2024

#![feature(gen_blocks)]

use std::pin::Pin;
use std::pin::pin;
use std::marker::PhantomPinned;

struct MyFuture {
    _pinned: PhantomPinned,
}

impl std::future::Future for MyFuture {
    type Output = u32;
    fn poll(self: Pin<&mut Self>, _cx: &mut std::task::Context<'_>) -> std::task::Poll<u32> {
        std::task::Poll::Ready(42)
    }
}

fn main() {
    // Test 1: pin!() in a gen block where the pin is used immediately (no yield crossing)
    let _iter = gen {
        let x = pin!(42u32);
        let val: u32 = *x;
        yield val;
    };

    // Test 2: pin!() in an async block (immovable coroutine, pin is always valid)
    let _fut = async {
        let x = pin!(MyFuture { _pinned: PhantomPinned });
        let _ = x;
    };

    // Test 3: pin!() with correct type annotation in gen block
    let _iter2 = gen {
        let _x: Pin<&mut u32> = pin!(42u32);
        yield 1u32;
    };

    // Test 4: pin!() with trait object coercion on the RESULT (safe, post-Pin)
    let _fut2 = async {
        let x = pin!(MyFuture { _pinned: PhantomPinned });
        let _: Pin<&mut dyn std::future::Future<Output = u32>> = x;
    };
}
