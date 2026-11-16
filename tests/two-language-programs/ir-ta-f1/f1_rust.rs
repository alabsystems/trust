//! F1 CONTROL (added by the Part A reviewer): the Rust-only half of f1_lib.rs behind the same C ABI,
//! with no Clean call edge and no upstream (`core`) callee, so the trust-ir codegen frontend has
//! nothing to refuse. Machine code FROM its trust-ir spelling, linked with the foreign main, must
//! print what the SAME crate prints when built by the default (LLVM) backend — a native oracle, not
//! a typed constant. (5 ^ 0x55) ^ 7 = 87.
#[inline(never)]
pub fn f1_rust_half(x: u64) -> u64 {
    x ^ 0x55
}
#[unsafe(no_mangle)]
pub extern "C" fn parta_f1_program() -> u64 {
    f1_rust_half(5) ^ 7
}
