//@ compile-flags: --crate-type=rlib -Ztrust-verify=on
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency VERIFIED on the default policy. `add1` is verified UNDER its
//! `requires`: its `x + 1` overflow row is kernel-certified with `x < 100` as the
//! entry hypothesis, so the compiler ELIDES that overflow check, and a DIRECT caller
//! in any crate is charged a `Precondition` row for the clause (read from this
//! crate's exported contract set). `add1_wrapping` is its `requires`-free twin. The
//! `dep_*` revisions of `assume_total_does_not_cover_callee_requires.rs` call them
//! from a body carrying `#[trust::assume_total]`.

pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}

pub fn add1_wrapping(x: u32) -> u32 {
    x.wrapping_add(1)
}
