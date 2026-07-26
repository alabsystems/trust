// tRust compatibility guard for rust-lang#134225-shaped code.
//
// Current upstream-compatible Rust accepts an unsafe alloc_error_handler with
// this signature. If tRust later rejects it as a verifier policy, that rejection
// must stay out of vanilla upstream compatibility mode.
//@ check-pass
//@ compile-flags:-C panic=abort

#![feature(alloc_error_handler)]
#![no_std]
#![no_main]

use core::alloc::Layout;

#[alloc_error_handler]
unsafe fn my_handler(_layout: Layout) -> ! {
    loop {}
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
