//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ rustc-env:TRUST_VERIFY_MEMORY_SAFE=1
//@ dont-check-compiler-stderr
//@ check-fail
//
// Ambient memory-safe policy is fail-closed REFUSED, not silently ignored:
// `TRUST_VERIFY_MEMORY_SAFE` is an untracked legacy semantic control, so a
// verifying session rejects the environment variable outright and names the
// tracked replacement — even when that replacement
// (`-Ztrust-policy=memory-safe`, present above) is already on the command
// line. MIR/codegen policy must come only from dependency-tracked compiler
// options.
pub fn unwrap_opt(o: Option<u32>) -> u32 {
    o.unwrap()
}
//~? ERROR environment variable `TRUST_VERIFY_MEMORY_SAFE` is an untracked Trust semantic/codegen control; remove it and use the corresponding tracked compiler option
