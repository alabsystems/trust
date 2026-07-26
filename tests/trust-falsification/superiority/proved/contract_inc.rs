#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// SUPERIORITY: upstream rustc's legacy contract implementation only offered
// a user-selected runtime projection. Trust retires that projection and
// STATICALLY PROVES this contract — the postcondition `ret > x` holds for
// `x + 1` under `requires(x < 100)` (no overflow, x+1 > x) — eliminating the
// runtime checks. Default mode must report it fully proved (0 runtime-checked).
#[core::contracts::requires(x < 100)]
#[core::contracts::ensures(move |ret: &u32| *ret > x)]
pub fn contract_inc(x: u32) -> u32 { x + 1 }
