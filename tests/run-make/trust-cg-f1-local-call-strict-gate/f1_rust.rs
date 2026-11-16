//! The Part A F1 CONTROL, verbatim from trust-ir's `first-party/trust-ir/reports/
//! 2026-09-17-two-language-proof-program/parta/f1/f1_rust.rs`: the
//! Rust-only half of the two-language crate behind the same C ABI, with no
//! Clean call edge and no upstream (`core`) callee, so the trust-ir codegen
//! frontend has nothing to refuse — except, before WS7.12, the local `Call`
//! itself. `(5 ^ 0x55) ^ 7 == 87`.
#![crate_name = "parta_f1_control"]

#[inline(never)]
pub fn f1_rust_half(x: u64) -> u64 {
    x ^ 0x55
}

#[unsafe(no_mangle)]
pub extern "C" fn parta_f1_program() -> u64 {
    f1_rust_half(5) ^ 7
}
