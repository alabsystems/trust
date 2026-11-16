//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Policy B tolerates the std print backend ONLY in a function with no source or
//! inlined `unsafe` (the memory-safe W2.1 gate, `function_uses_unsafe`). A caller
//! that uses `unsafe` keeps every assumption-panic row fatal, because an unproved
//! gap there could sit beside UB that no runtime check catches. The `unsafe fn` is
//! trivially panic-free on its own, so the gate is the only thing keeping this red.
unsafe fn nop() {}
fn main() {
    unsafe { nop() }
    println!("hello");
}
