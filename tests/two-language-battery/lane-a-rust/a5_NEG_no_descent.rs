//@ battery-lane: A-rust
//@ battery-expect: reject
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A NEGATIVE CONTROL — non-termination must stay visible.
//!
//! The measure is authored but never descends: the recursive call passes `n`
//! unchanged, so this function does not terminate for `n > 0`. The
//! termination obligation must FAIL.
//!
//! This is the exact soundness class of the four termination-callgraph
//! false-accepts fixed in trust-wp on 2026-07-24 (a non-terminating logic
//! definition that verified). If this file passes, that class is back.

pub fn no_descent(n: u32)
    decreases n
{
    if n > 0 {
        no_descent(n);
    }
}
