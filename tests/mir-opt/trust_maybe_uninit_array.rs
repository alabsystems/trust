// Trust: Regression test for #932 (rust-lang#152541)
// Trust: Verify that [MaybeUninit::uninit(); N] does not generate memset(0)
// Trust: in codegen. The MIR should use Repeat with a MaybeUninit constant.
//@ compile-flags: -O

use std::mem::MaybeUninit;

// EMIT_MIR trust_maybe_uninit_array.large_uninit_array.GVN.diff
pub fn large_uninit_array() -> [MaybeUninit<u8>; 4096] {
    // CHECK-LABEL: fn large_uninit_array(
    // Trust: The GVN pass should produce a const <uninit> or Repeat pattern.
    // Trust: Either way, codegen must NOT emit memset(0) for this.
    [MaybeUninit::uninit(); 4096]
}

// EMIT_MIR trust_maybe_uninit_array.large_uninit_u64_array.GVN.diff
pub fn large_uninit_u64_array() -> [MaybeUninit<u64>; 1024] {
    // CHECK-LABEL: fn large_uninit_u64_array(
    [MaybeUninit::uninit(); 1024]
}
