#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT: `ret > 0` is FALSE for `-x` under `requires(x > 0)` (negating a
// positive yields a negative). Trust must NOT statically discharge it — the
// postcondition is refuted (sound: the pin connects `_0` to its definition, it
// does not make a wrong spec verify).
#[core::contracts::requires(x > 0)]
#[core::contracts::ensures(move |r: &i32| *r > 0)]
pub fn negate(x: i32) -> i32 { -x }
