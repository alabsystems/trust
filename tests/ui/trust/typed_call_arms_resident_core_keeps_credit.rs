//@ needs-trust-verify
//@ edition: 2021
//@ revisions: call_gate census
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=strict
//@ rustc-env:TRUST_PF_MATCH_TRACE=1
//@[call_gate] rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//~? RAW [PF_ZEROGATE] fn=typed_call_arms_resident_core_keeps_credit::cell_control arm=cell-set-typed callee=core::cell::Cell::<u32>::set
//[call_gate]~? RAW [PF_CALLGATE] fn=typed_call_arms_resident_core_keeps_credit::unwrap_or_control arm=moved-value-nodrop discharges callee: core::option::Option::<u32>::unwrap_or
//[call_gate]~? RAW [PF_CALLGATE] fn=typed_call_arms_resident_core_keeps_credit::ok_or_control arm=moved-value-nodrop discharges callee: core::option::Option::<u32>::ok_or::<u32>
//[call_gate]~? RAW [PF_CALLGATE] fn=typed_call_arms_resident_core_keeps_credit::result_unwrap_or_control arm=moved-value-nodrop discharges callee: core::result::Result::<u32, u32>::unwrap_or
//[call_gate]~? RAW [PF_CALLGATE] fn=typed_call_arms_resident_core_keeps_credit::result_ok_control arm=moved-value-nodrop discharges callee: core::result::Result::<u32, u32>::ok
//[census]~? RAW [PF_ZEROGATE] fn=typed_call_arms_resident_core_keeps_credit::unwrap_or_control arm=moved-value-nodrop callee=core::option::Option::<u32>::unwrap_or
//[census]~? RAW [PF_ZEROGATE] fn=typed_call_arms_resident_core_keeps_credit::ok_or_control arm=moved-value-nodrop callee=core::option::Option::<u32>::ok_or::<u32>
//[census]~? RAW [PF_ZEROGATE] fn=typed_call_arms_resident_core_keeps_credit::result_unwrap_or_control arm=moved-value-nodrop callee=core::result::Result::<u32, u32>::unwrap_or
//[census]~? RAW [PF_ZEROGATE] fn=typed_call_arms_resident_core_keeps_credit::result_ok_control arm=moved-value-nodrop callee=core::result::Result::<u32, u32>::ok
//~? RAW [PF_ZEROGATE] fn=typed_call_arms_resident_core_keeps_credit::into_iter_control arm=registry callee=<&[u32] as core::iter::traits::collect::IntoIterator>::into_iter
//! HONEST CONTROL for the residency conjunct on the three typed call-credit
//! identities pinned by `typed_call_arms_core_substitution_impostor_refuted.rs`:
//! the same calls on this compiler's own resident `core` must keep their credit,
//! through the same arms, and the crate must build under strict.
//!
//! `Cell::<u32>::set` and `<&[u32]>::into_iter` reach the zero-obligation gate
//! (`[PF_ZEROGATE]`); the four moved-value methods carry one proved row each and
//! reach the non-empty lane's call gate (`[PF_CALLGATE]`). MEASURED on stage-1
//! `trustc` at `978840fe007` (origin/main) and with the fix: the same six arm
//! lines, and the build passes.
//!
//! Trust (2026-09-29, std-absent-callee): the sysroot panic census
//! (docs/design/trust-std-design.md, amendment 2026-09-26) derives from their own
//! MIR that `Option::unwrap_or`, `Option::ok_or`, `Result::unwrap_or` and
//! `Result::ok` reach no panic site, and discharges those calls on the bridge's
//! compiler-total channel. Their functions then carry no row, and reach the
//! ZERO-obligation gate, where the same `moved-value-nodrop` arm credits the same
//! callee. So the test has two revisions. Neither weakens a check.
//!
//! * `call_gate` runs with the census off (`TRUST_NO_SYSROOT_CENSUS=1`, which
//!   only withholds census grants), so the non-empty lane's call-gate arm is
//!   still measured on the resident core. That lane is the one the impostor
//!   refutation's `arm=NONE` lines pin, which is why this control exists.
//! * `census` runs with the census on and pins the route the calls now take:
//!   the zero-obligation gate's `moved-value-nodrop` arm, on the resident core.
#![no_std]

use core::cell::Cell;

pub fn cell_control(c: &Cell<u32>) {
    c.set(1);
}

pub fn unwrap_or_control(o: Option<u32>) -> u32 {
    o.unwrap_or(7)
}

pub fn ok_or_control(o: Option<u32>) -> Result<u32, u32> {
    o.ok_or(3)
}

pub fn result_unwrap_or_control(r: Result<u32, u32>) -> u32 {
    r.unwrap_or(5)
}

pub fn result_ok_control(r: Result<u32, u32>) -> Option<u32> {
    r.ok()
}

pub fn into_iter_control(s: &[u32]) {
    let _it = core::iter::IntoIterator::into_iter(s);
}
