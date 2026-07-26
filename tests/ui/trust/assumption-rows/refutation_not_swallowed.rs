// Trust (assumption ledger, Stage 1): the assumption demotion must never
// swallow a genuine refutation. The async fn records a coroutine assumption
// row, but the unguarded division in `mid` is refuted and still fails the
// report under the nonfatal lame policy (division panics regardless of overflow-checks,
// so this refutation needs no extra flags). build-pass: the verify pass runs
// when codegen demands optimized_mir, so a non-generic body's refutation
// fires at BUILD time (the check build passes — only metadata-encoded bodies
// like the async closure are visited there).
//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory --crate-type=lib
//@ build-pass
//@ dont-check-compiler-stderr
pub async fn helper(x: u32) -> u32 {
    x
}
pub fn mid(a: u64, b: u64) -> u64 {
    //~^ WARN Trust Level 0 safety verification incomplete
    a / b
}
//~? RAW Trust: ASSUMPTION [coroutine]
