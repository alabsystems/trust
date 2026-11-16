//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! A std signed-integer `abs` result is its argument's magnitude, so the sum of two
//! absolute differences of widened `i32`s cannot overflow an `i64` (ordsweep2
//! structs/c02). Without the value fact `dx` was free and `dx + dy` was refuted with
//! `dx = i64::MAX`. The call's own `MIN` overflow row stays a runtime-checked
//! advisory under the default policy. The twin `_refused.rs` keeps sums that can
//! overflow refused.
pub fn manhattan(a: i32, b: i32, c: i32, d: i32) -> i64 {
    let dx = (a as i64 - b as i64).abs();
    let dy = (c as i64 - d as i64).abs();
    dx + dy
}
