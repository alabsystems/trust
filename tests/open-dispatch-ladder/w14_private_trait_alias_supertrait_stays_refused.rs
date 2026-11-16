//@ trust-ladder: verifies
//@ trust-ladder-row: Trust verification advisory for `w14_private_trait_alias_supertrait_stays_refused::f`: 1 instance hypothesis row(s)
//! RE-RECORDED 2026-10-05 at integration (the stage 1 of `76a6ea45b2`: wave 14 on
//! main `d5da8dc314`). OD-1 phase 1 (main `c77d7678cf`) landed after this row was
//! written: an OPEN generic call is now admitted as one `assumption:instance-hypothesis`
//! row, so under this ladder's flags `f` exits 0 with a CONDITIONAL result instead of
//! failing. The row therefore records `verifies` and demands that hypothesis
//! warning. A trait the verifier still calls `Sealed` (the hole) mints no hypothesis
//! row, so the needle is what separates the fix from the hole. Measured with
//! `TRUST_RUNG2_PROBE=1`: BEFORE (the stage 1 of `d5da8dc314`) rc=0,
//! `sealedness=Sealed` (the Φ rows print none), no hypothesis row, so the ladder
//! reports `the decisive row is gone`; AFTER rc=0, `sealedness=Open`, the needle
//! present. Under `-Ztrust-verify=on -Ztrust-policy=certify` BEFORE rc=0 and AFTER
//! rc=1 (`Trust certify verification failed for ..::f: 1 instance hypothesis
//! row(s)`). The compiletest twin is
//! `tests/ui/trust/private_supertrait_seal_needs_a_closed_impl_set.rs`. The text
//! below is the row as first written; its `refuses` and "rc=1" AFTER predate OD-1.
//! DEP-SEAL-1 (found by the wave-14 implementer, beyond the scout's sketch): a
//! private TRAIT ALIAS is not a seal. `Sealed = Clone` has no impls of its own;
//! every `Clone` type satisfies it, so a downstream `#[derive(Clone)] struct Bad;
//! impl a::T for Bad { .. }` is legal.
//!
//! BEFORE, measured 2026-10-04 on this file with the wave-14 scout's `stage1-w12`
//! (`rustc 1.99.0-dev`, trust 0.10.0; per the scout, main `361160e17a` plus wave
//! 12): rc=0 under this ladder's flags (`TRUST_RUNG2_PROBE=1`:
//! `sealedness=Sealed`), and rc=0 under `-Ztrust-verify=on -Ztrust-policy=certify`.
//! Built `--crate-name a` under certify, a verify-off binary with `#[derive(Clone)]
//! struct Bad; impl a::T for Bad { panic!() }` printed `f(&Good) = 7` and then
//! panicked inside the certified `a::f` (exit 101).
//!
//! AFTER (predicted, not built): rule (a') (the supertrait is a trait alias, not a
//! trait) drops the private-supertrait route, `T` is exported and this is an rlib,
//! so the impl set is `Open` and `f` keeps its obligation. Proxy, measured on the
//! BEFORE compiler: this file with the `: private::Sealed` bound deleted gives rc=1
//! and this row's `trust-ladder-row`.
#![feature(trait_alias)]

mod private {
    pub trait Sealed = Clone;
}
pub trait T: private::Sealed {
    fn m(&self) -> u32;
}
#[derive(Clone)]
pub struct Good;
impl T for Good {
    fn m(&self) -> u32 {
        7
    }
}
pub fn f<K: T>(x: &K) -> u32 {
    x.m()
}
