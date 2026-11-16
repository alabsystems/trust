//@ compile-flags: --crate-type=rlib -Ztrust-verify=on -Ztrust-policy=certify -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency VERIFIED under `certify` that builds clean (rc=0): `inc` is verified
//! UNDER its `requires`, so its `x + 1` overflow row is kernel-certified with
//! `x < 100` as the entry hypothesis and `elide_kernel_certified_checks` DROPS that
//! overflow `Assert` from the MIR this crate encodes. A direct caller in any crate is
//! charged a `Precondition` row for the clause (read from this crate's exported
//! contract set); a call from another dependency's body that a verifying crate
//! bundles as a MEMBER is charged nothing (DEP-MEMBER-REQ-1,
//! `xcrate_declared_member_requires_callee.rs`).
//!
//! `#[inline]` exports `inc`'s elided body for a downstream MIR inliner
//! deterministically (`xcmreq_mid_o3.rs` inlines it).
//!
//! `cap` is the requires-free control: a member calling it stays bundled.
//! `halve` is the requires-free `#[inline]` control for the C-FLOW revisions:
//! `xcmreq_dyn_o3.rs` inlines it, and a re-derived body that inlined it stays
//! re-derivable.
//!
//! **Since ADVISORY-REQUIRES-CROSS-CRATE (main, 2026-10-05) `inc` no longer elides.**
//! A `requires` body another crate can call (here: `pub` in an rlib) keeps every
//! check its clause proved, so `inc`'s overflow `Assert` stays in the encoded MIR and
//! a call that breaks the clause panics. What still elides is a body NO other crate
//! can call: the private `bump` below, reached from outside only through the `pub`
//! `inc_via`, whose own `requires` charges `bump`'s clause here, in this crate.
//! Measured 2026-10-05 on the stage 1 of `c1c028f41f` with `TRUST_ELIDE_DEBUG=1`:
//! `elided 1 kernel-certified overflow checks in … xcmreq_callee::bump`, and none in
//! `inc` or `inc_via`. A caller that breaks `inc_via`'s clause is charged nothing in
//! a verify-off crate, so `bump`'s wrapped `x + 1` was reachable: the wrong value
//! DEP-MEMBER-REQ-1's run witness pinned came through `inc_via`.
//!
//! **Since ADVISORY-REQUIRES-TRANSITIVE-1 (2026-10-05) `bump` no longer elides
//! either** (measured 2026-10-06 on the stage 1 of `0ac7a96d9f`: no `TRUST_ELIDE`
//! line for `bump`): `bump` is named by `inc_via`, a `requires` body
//! another crate can call, so the charge of its clause rests on a hypothesis only the
//! consumer's policy enforces, and it keeps its check. Nothing in this crate elides
//! under a clause any more; the run witness's `private_callee` revision panics.
#![crate_name = "xcmreq_callee"]

#[inline]
pub fn inc(x: u32) -> u32
    requires x < 100
{
    x + 1
}

/// Owes nothing that is not already its own clause, and has no arithmetic: the
/// check that matters is `bump`'s, which this entry exposes (see the module docs).
pub fn inc_via(x: u32) -> u32
    requires x < 100
{
    bump(x)
}

fn bump(x: u32) -> u32
    requires x < 100
{
    x + 1
}

pub fn cap(x: u32) -> u32 {
    if x > 100 { 100 } else { x }
}

#[inline]
pub fn halve(x: u32) -> u32 {
    x / 2
}
