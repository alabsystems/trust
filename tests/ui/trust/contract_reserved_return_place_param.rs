//@ needs-trust-verify
//@ revisions: result zero destructured
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//! `_0` and `result` are the canonical contract return-place vocabulary. A
//! Rust parameter may use either spelling in ordinary code, but not on a
//! function with contracts: every semantic lane must reject the collision
//! instead of rebinding it as an input or silently dropping a monitor.

#[cfg(result)]
fn reserved_result(result: u64) -> u64
    //[result]~^ ERROR parameter `result` collides with the source-contract return-place vocabulary
    ensures 0 == 0
{
    result
}

#[cfg(zero)]
fn reserved_zero(_0: u64) -> u64
    //[zero]~^ ERROR parameter `_0` collides with the source-contract return-place vocabulary
    ensures 0 == 0
{
    _0
}

#[cfg(destructured)]
fn reserved_destructured((result, x): (u64, u64)) -> u64
    //[destructured]~^ ERROR parameter `result` collides with the source-contract return-place vocabulary
    ensures 0 == 0
{
    result + x
}

fn main() {}
