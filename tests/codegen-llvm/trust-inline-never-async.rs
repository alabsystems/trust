// Trust: regression test for rust-lang#129347
// `#[inline(never)]` on async fn should be respected by the coroutine body,
// not just the outer wrapper that constructs the future.
//
// Before the fix, the desugared coroutine had `InlineAttr::None` (default),
// so LLVM was free to inline the actual async fn body even when the user
// explicitly asked it not to be inlined.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ compile-flags: -Copt-level=3 -Csymbol-mangling-version=v0
//@ edition: 2021

#![crate_type = "lib"]

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

unsafe extern "Rust" {
    fn opaque_u64() -> u64;
}

struct OpaqueReady;

impl Future for OpaqueReady {
    type Output = u64;

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
        Poll::Ready(unsafe { opaque_u64() })
    }
}

#[no_mangle]
pub fn drive_inline_never_async(cx: &mut Context<'_>) -> Poll<u64> {
    let mut fut = call_inline_never_async();
    unsafe { Pin::new_unchecked(&mut fut) }.poll(cx)
}

async fn call_inline_never_async() -> u64 {
    inline_never_work().await.wrapping_mul(2)
}

// CHECK: ; trust_inline_never_async::inline_never_work::{closure#0}
// CHECK-NEXT: ; Function Attrs: {{.*}}noinline
#[inline(never)]
async fn inline_never_work() -> u64 {
    OpaqueReady.await
}
