#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// SUPERIORITY: a boolean-valued postcondition on a `-> bool` predicate. The
// postcondition parser models `result`/`_0` as a default (Int) sort, but the
// return slot is Bool — so `ensures(ret == (x > 0))` was false-refuted (the
// body fact `__ret == (x > 0)` lived under a Bool var disconnected from the
// postcond's Int `_0`). Trust now re-sorts `_0` to the real return sort and
// STATICALLY PROVES the contract, eliminating the runtime check (0 runtime-checked).
#[core::contracts::ensures(move |r: &bool| *r == (x > 0))]
pub fn is_positive(x: i32) -> bool { x > 0 }
