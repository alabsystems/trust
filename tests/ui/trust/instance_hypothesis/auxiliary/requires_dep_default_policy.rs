//@ compile-flags: --crate-type=rlib -Ztrust-verify=on -Coverflow-checks=on
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency VERIFIED on the default policy (ADVISORY-REQUIRES-CROSS-CRATE).
//! Each `x + 1` below is kernel-certified not to overflow UNDER `x < 100`. Before
//! the fix `elide_kernel_certified_checks` dropped that check from every one of
//! these bodies, though a consumer crate's policy decides whether its calls are
//! charged the clause: an advisory consumer only warns, a verify-off one charges
//! nothing. Every item here is reachable from another crate, so each keeps its
//! check; `outer` is the control — its private callee is charged here, in this
//! crate, and `outer` itself owes nothing.

pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}

pub struct S;

impl S {
    pub fn add1m(&self, x: u32) -> u32
        requires x < 100
    {
        x + 1
    }
}

fn inner(x: u32) -> u32
    requires x < 100
{
    x + 1
}

pub fn outer(x: u32) -> u32 {
    if x < 100 { inner(x) } else { 0 }
}
