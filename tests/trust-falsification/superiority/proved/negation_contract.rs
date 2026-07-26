#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// SUPERIORITY: a postcondition that does NOT mention the parameter. The return
// value `_0 = -x` (a UnaryOp, not a `Use`) was captured by block-def extraction
// as `__ret == Neg(x)`, but the relevance filter PRUNED it because the postcond
// `ret < 0` shares no variable with it (`_0` vs `__ret`/`x`) — leaving `_0`
// havoc'd and the valid postcondition FALSE-REFUTED. Trust now pins
// `_0 == <rvalue>` for any direct return assignment, so it STATICALLY PROVES
// `ret < 0` under `requires(x > 0)` (default mode, 0 runtime-checked).
#[core::contracts::requires(x > 0)]
#[core::contracts::ensures(move |r: &i32| *r < 0)]
pub fn negate(x: i32) -> i32 { -x }
