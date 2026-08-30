//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-FC): `extern "C" { unwind: false }` fn-pointer signatures join
//! the admitted fragment. The convention rides the CALL EDGE
//! (`CallIndirect.calling_conv`, derived from the callee type's own header —
//! never hardcoded) and the spliced-body stamp now carries the body's REAL
//! ABI, so a local `extern "C"` fn is no longer falsely claimed
//! `CallingConv::Rust` (the #180/#190 honesty line, extended).

extern "C" fn add(a: u64, b: u64) -> u64 {
    a + b
}

fn call_through(f: extern "C" fn(u64, u64) -> u64, x: u64) -> u64 {
    f(x, 1)
}

fn main() {
    assert_eq!(call_through(add, 41), 42);
    let g: extern "C" fn(u64, u64) -> u64 = add;
    assert_eq!(g(20, 22), 42);
}
