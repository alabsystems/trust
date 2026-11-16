//@ compile-flags: --crate-type=rlib -Ztrust-verify=on
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency VERIFIED on the default policy, as a library another team ships
//! verified. `add1` is verified UNDER its `requires`: its `x + 1` overflow row is
//! proved (kernel-certified) with `x < 100` as the entry hypothesis, so the
//! compiler ELIDED that overflow check, and every DIRECT caller in any crate is
//! charged a `Precondition` row for the clause (read from this crate's exported
//! contract set). Reached with no call site to charge — through a fn pointer, or
//! handed to generic code — `add1(u32::MAX)` returns 0 instead of panicking.
//! (Until 2026-10-05. Since ADVISORY-REQUIRES-CROSS-CRATE a `requires` body
//! another crate can call keeps its checks, so that call panics.)
//! `add1_wrapping` is its `requires`-free twin. The verify-off build of the same
//! body is `auxiliary/requires_callee_dep_off.rs`.

pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}

pub fn add1_wrapping(x: u32) -> u32 {
    x.wrapping_add(1)
}
