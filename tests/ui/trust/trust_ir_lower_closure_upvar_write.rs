//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-CX): a write to a captured upvar inside an `FnMut` closure body
//! (`sum = sum + i`, `c += 1`) goes THROUGH the captured `&mut T` pointer in
//! the env tuple (or replaces a by-value element and writes the tuple back),
//! and the enclosing body promotes the locals a closure literal captures by
//! `&mut`, exactly as any other `&mut` borrow does. Every body here carried
//! `Assign(non-local place)` / `AssignOp(non-local place)` (closure) or
//! `Borrow(&mut unpromoted local)` (caller) before the wave; `strict` turns
//! that into a compile error, so this file is the mutation check.
//!
//! SOURCE ABI (EXACT-THIR-ABI-1, 51558bd9ff): `run`'s `it(..)` is the generic
//! `FnMut::call_mut` havoc callee, declared `extern "rust-call"`. That source ABI has no IR
//! convention until a real tuple adapter exists, so the producer refuses `run` at the callee
//! (expected below; one `Callee(unsupported source ABI)` per call, and the non-Rust bodyless
//! declaration's `Args` parameter is the foreign-layout refusal). The closures and their
//! callers stay unannotated, so this file keeps its mutation check. Strict's per-body error
//! ends the compile at the analysis error gate, before D28 runs: `run`'s own D28 refusal
//! (`Abstracted(drop, ..)` of its by-value `impl FnMut`) is still measured without strict.
fn run(mut it: impl FnMut(isize)) {
    //~^ ERROR the direct trust-ir producer could not fully lower this body (3 unsupported shape(s)): Callee(foreign-ABI repr(Rust) struct by value) at std::ops::FnMut::call_mut; Callee(unsupported source ABI) at callee
    it(1);
    it(2);
}
fn total() -> isize {
    let mut sum: isize = 0;
    run(|i| {
        sum = sum + i;
    });
    sum
}
fn count() -> u8 {
    let mut c = 0u8;
    run(|_| c += 1);
    c
}
fn main() {
    let ok = total() == 3 && count() == 2;
    std::process::exit(!ok as i32);
}
