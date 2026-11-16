//@ compile-flags: --crate-type=rlib -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ edition: 2021
//@ no-prefer-dynamic
//! A library VERIFIED under the advisory policy (so an unproved row is a warning, not
//! a build failure) whose `f` carries a `clippy::` attribute spelled like a Trust
//! precondition with the compiler-internal lowering prefix (CONTRACT-NS-1). If the
//! extractor treats it as a precondition, `x + 4_294_967_000` is proved under
//! `x < 100` and its overflow check is elided from the emitted code.

#[clippy::requires = "__trust_lowered_compiler_contract__:x < 100"]
pub fn f(x: u32) -> u32 {
    x + 4_294_967_000
}
