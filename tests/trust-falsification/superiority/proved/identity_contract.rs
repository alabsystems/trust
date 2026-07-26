#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// SUPERIORITY: an identity-preserving contract. rustc's contracts desugaring
// COALESCES the `__ret` result binding onto the parameter local for a trivial
// body (`fn f(x){x}` returns its param), so the param local's source name `x`
// could be shadowed by `__ret` — false-refuting `ensures(ret == x)`. Trust
// preserves the source name and STATICALLY PROVES the postcondition (the return
// value equals the input under `requires(x < 100)`), eliminating the runtime
// contract check. Default mode must report it fully proved (0 runtime-checked).
#[core::contracts::requires(x < 100)]
#[core::contracts::ensures(move |ret: &u32| *ret == x)]
pub fn identity_contract(x: u32) -> u32 { x }
