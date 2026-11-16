//@ revisions: default certify o2plain
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@[o2plain] compile-flags: -Copt-level=2
//@ check-pass
//@ dont-check-compiler-stderr
//! D5-B (2026-09-24): a contract-less same-crate helper whose return equality
//! `_0 == E(params)` the Clean CIC kernel certifies against the helper's OWN
//! body gets that lemma as a call-site fact, so its callers prove exactly as the
//! inline twin (and the hand-written `ensures result == …` twin in
//! `call_dest_pinned_callees_prove.rs`) does.
//!
//! BEFORE (stage-1 `4e9fe36bf`, which has D5-A but not D5-B), `default` and
//! `certify`: rc=1. `shift_via_guard`, `cell_index` and `sub_via_le` each read
//! `[…] UNKNOWN (trust-full-verifier): generic solver counterexample withheld:
//! query depends on the unmodeled return of same-crate `…::guard` / `…::cell_width_ok`
//! / `…::le`` and errored (the D5-A held row; before D5-A they were FALSE
//! refutations, `counterexample: _3 = true, … bit = 64`). `opt`: rc=0 already —
//! at `-O2` the helpers are inlined, so this revision pins that the lemma does
//! not disturb the inlined route.
//!
//! AFTER: rc=0 in all three revisions. The injected clause is the SAME formula
//! the authored twin lowers to (`Eq(Var("_0", Bool), Lt(Var("bit", Int),
//! Int(64)))`), through the same composition lane; the vcgen-level real-MIR
//! matrix (`crates/trust-vcgen/tests/inferred_return_realmir.rs`) measures every
//! caller row here as ay-Proved AND kernel-certified with the lemma, and
//! unproved without it.
//!
//! Adversarial twins that must NOT prove live in
//! `inferred_return_real_bug_refutes.rs` and
//! `inferred_return_never_proves_nonfragment.rs`.

pub fn guard(bit: u32) -> bool {
    bit < 64
}

pub fn shift_via_guard(x: u64, bit: u32) -> Option<u64> {
    if !guard(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn cell_width_ok(cell: u32) -> bool {
    cell > 0
}

pub fn cell_index(rel: u32, cell: u32) -> Option<u32> {
    if !cell_width_ok(cell) {
        return None;
    }
    Some(rel / cell)
}

pub fn le(a: u32, b: u32) -> bool {
    a <= b
}

pub fn sub_via_le(a: u32, b: u32) -> Option<u32> {
    if !le(a, b) {
        return None;
    }
    Some(b - a)
}

// A DIAMOND helper (D5-B follow-up, 2026-09-25): certifies only through the
// kernel-checked rewriting lane (the pre-optimization body is `_2 = copy d`
// plus a branch); the caller's divisor proof needs the case split on `d == 0`.
// Before the lane: held UNKNOWN in `call_dest_refutation_held.rs`.
// Not in the `opt` revision: at `-O2` `nz` is INLINED, so there is no call and no
// lemma, and the inlined diamond divisor gets an UNGROUNDED `[divzero] FAILED`
// (a pre-existing false refutation of vcgen on the inlined select, measured
// 2026-09-25 — not a D5-B row).
pub fn nz(d: u32) -> u32 {
    if d == 0 { 1 } else { d }
}

pub fn div_nz(x: u32, d: u32) -> u32 {
    x / nz(d)
}

pub fn shift_inline(x: u64, bit: u32) -> Option<u64> {
    if !(bit < 64) {
        return None;
    }
    Some(x >> bit)
}
