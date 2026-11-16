//@ revisions: std_skip option_flags shared_recv nsa
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[std_skip] rustc-env:TRUST_STD_UNSAFE_CALL_SKIP=1
//@[option_flags] rustc-env:TRUST_OPTION_FLAG_LANES=0
//@[shared_recv] rustc-env:TRUST_SHARED_RECV_PLACE=0
//@[nsa] rustc-env:TRUST_NSA=0
//@ check-fail
//@ dont-check-compiler-stderr

// Trust: presence is forbidden while verification or trust-ir lowering is
// active, including a value that disables a default-on producer lane. These
// controls are not dependency-tracked compiler options. Refuse before a body
// can gain or lose obligations; the diagnostic must name the actual input.
pub fn identity(value: u32) -> u32 {
    value
}
//[std_skip]~? ERROR environment variable `TRUST_STD_UNSAFE_CALL_SKIP` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[option_flags]~? ERROR environment variable `TRUST_OPTION_FLAG_LANES` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[shared_recv]~? ERROR environment variable `TRUST_SHARED_RECV_PLACE` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
//[nsa]~? ERROR environment variable `TRUST_NSA` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
