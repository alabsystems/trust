// Positive control for n01_NEG: a TRUE contract must build under the default (strict) policy.
pub fn double(x: i32) -> i32
    requires x > 0
    requires x < 1000
    ensures result == x * 2
{ x * 2 }
