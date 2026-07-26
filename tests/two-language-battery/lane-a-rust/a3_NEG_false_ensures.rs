//@ battery-lane: A-rust
//@ battery-expect: reject
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A NEGATIVE CONTROL — the battery's own integrity check.
//!
//! Every clause below is FALSE for some admissible input. A toolchain that
//! accepts this file proves nothing by accepting the positive files either,
//! so this program is load-bearing: it is the difference between a battery
//! and a demo.
//!
//! `wrong_sum` claims a sum it does not compute; `wrong_bound` claims a
//! postcondition its precondition does not support (the wrap point is left
//! IN, which is exactly the case the unbounded-Int reading used to miss).

/// FALSE: the body subtracts where the clause claims addition.
pub fn wrong_sum(a: u64, b: u64) -> u64
    requires a <= 1000
    requires b <= 1000
    requires a >= b
    ensures result == a + b
{
    a - b
}

/// FALSE at the wrap point: `x == u64::MAX` makes `x + 1` wrap to 0.
pub fn wrong_bound(x: u64) -> u64
    ensures result > x
{
    x + 1
}
