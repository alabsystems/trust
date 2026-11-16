//@ revisions: default certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-pass
//! The positive twin of `call_dest_refutation_held.rs`: a same-crate helper
//! whose result IS modeled proves its caller, under the default policy AND
//! under `-Ztrust-policy=certify` (measured on stage-1 `a8c853de6f`: rc=0 in
//! both, every caller row kernel-certified). The D5-A screen only ever reads a
//! `Failed` row, so it cannot move any of these; this file pins that the
//! modeled routes stay the way to discharge a helper-guarded operation.
//!
//! * `guard` states its result with `ensures result == (bit < 64)` — the
//!   authored-`ensures` composition lane (the workaround the held-row reason
//!   recommends).
//! * `one` has a crate-wide constant-set return summary.
//! * `shift_inline` is the inline control.

pub fn guard(bit: u32) -> bool
    ensures result == (bit < 64)
{
    bit < 64
}

pub fn shift_via_guard(x: u64, bit: u32) -> Option<u64> {
    if !guard(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn shift_inline(x: u64, bit: u32) -> Option<u64> {
    if !(bit < 64) {
        return None;
    }
    Some(x >> bit)
}

pub fn one() -> u32 {
    1
}

pub fn div_one(x: u32) -> u32 {
    x / one()
}
