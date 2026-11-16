//@ compile-flags: --crate-type=rlib -Ztrust-verify=on
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency VERIFIED on the default policy (level 2). `dep_add1` is verified
//! UNDER its `requires`: its `x + 1` overflow row is proved with `x < 100` as the
//! entry hypothesis, so the compiler ELIDES that overflow check, and a DIRECT caller
//! in any crate owes a `Precondition` row for the clause (read from this crate's
//! exported contract set). The `l0_dep` revision of `l0_callsite_requires_charged.rs`
//! calls it from a caller verified at `-Ztrust-verify-level=0`.

pub fn dep_add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}
