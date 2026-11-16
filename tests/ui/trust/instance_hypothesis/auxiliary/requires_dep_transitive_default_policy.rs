//@ compile-flags: --crate-type=rlib -Ztrust-verify=on -Coverflow-checks=on
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency VERIFIED on the default policy (ADVISORY-REQUIRES-TRANSITIVE-1).
//! Every `pub` entry below owes `x < 100` and reaches a PRIVATE `requires` body
//! that does the `x + 1`, each by its own route: a call (`leaf`), a chain of two
//! private `requires` bodies (`hop`, then `leaf2`), a method call (`leaf_m`) and a
//! type-relative path (`S::leaf_assoc`). Each leaf's check is kernel-certified
//! UNDER `x < 100`, and each call into it is charged that clause here, but under
//! the `pub` entry's own `x < 100`, which only the consumer's policy enforces.
//!
//! BEFORE (the stage 1 `scratchpad/stage1-w16`, which carries
//! ADVISORY-REQUIRES-CROSS-CRATE): `TRUST_ELIDE_DEBUG=1` reports 1 elided check in
//! each of `leaf`, `leaf2`, `leaf_m` and `leaf_assoc`, and none in the `pub`
//! entries or in `hop`, which has no arithmetic. AFTER: every private body here is
//! named by a chain of `requires` bodies that starts at a `pub` one, so none of
//! them elides.

pub fn add1_via(x: u32) -> u32
    requires x < 100
{
    leaf(x)
}

fn leaf(x: u32) -> u32
    requires x < 100
{
    x + 1
}

pub fn add1_chain(x: u32) -> u32
    requires x < 100
{
    hop(x)
}

fn hop(x: u32) -> u32
    requires x < 100
{
    leaf2(x)
}

fn leaf2(x: u32) -> u32
    requires x < 100
{
    x + 1
}

pub struct S;

impl S {
    pub fn add1m_via(&self, x: u32) -> u32
        requires x < 100
    {
        self.leaf_m(x)
    }

    fn leaf_m(&self, x: u32) -> u32
        requires x < 100
    {
        x + 1
    }

    fn leaf_assoc(x: u32) -> u32
        requires x < 100
    {
        x + 1
    }
}

pub fn add1_assoc(x: u32) -> u32
    requires x < 100
{
    S::leaf_assoc(x)
}
