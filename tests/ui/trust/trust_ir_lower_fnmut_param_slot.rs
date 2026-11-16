//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-PM): a by-value param of bare type-parameter type (`f: F`,
//! `F: FnMut`) that the body `&mut`-borrows (`f(x)` is `FnMut::call_mut(&mut
//! f, (x,))`) is promoted to a symbolic `Unit` slot, so the reborrow resolves
//! to a ledgered slot pointer that forwards into the generic `call_mut` havoc
//! call. The body stays SYMBOLIC (never spliced or sampled). Under `strict`.
//!
//! SOURCE ABI (EXACT-THIR-ABI-1, 51558bd9ff): that havoc callee, `FnMut::call_mut`, is
//! declared `extern "rust-call"`, which has no IR convention until a real tuple adapter exists,
//! so the producer refuses `call_twice` and `call_it` at the callee (expected below; one
//! `Callee(unsupported source ABI)` per call, and the non-Rust bodyless declaration's `Args`
//! parameter is the foreign-layout refusal). The full message is pinned, so a promotion
//! regression (`Promote(..)`/`Borrow(&mut unpromoted local)`) still changes it. Strict's
//! per-body error ends the compile at the analysis error gate, before D28 runs: their D28
//! refusal (`Abstracted(drop, ..)` of the by-value `F`) is still measured without strict.

fn call_twice<F: FnMut(u32) -> u32>(mut f: F, x: u32) -> u32 {
    //~^ ERROR the direct trust-ir producer could not fully lower this body (3 unsupported shape(s)): Callee(foreign-ABI repr(Rust) struct by value) at std::ops::FnMut::call_mut; Callee(unsupported source ABI) at callee
    f(x) + f(x)
}

fn call_it<F: FnMut()>(mut f: F) {
    //~^ ERROR the direct trust-ir producer could not fully lower this body (3 unsupported shape(s)): Callee(foreign-ABI repr(Rust) struct by value) at std::ops::FnMut::call_mut; Callee(unsupported source ABI) at callee
    f();
    f();
}

fn main() {
    // Capture-free closures only: a CAPTURING closure literal in argument
    // position is a different (wave-ZC) question and stays out of this pin.
    call_it(|| {});
    if call_twice(|v| v + 1, 20) != 42 {
        std::process::exit(1);
    }
}
