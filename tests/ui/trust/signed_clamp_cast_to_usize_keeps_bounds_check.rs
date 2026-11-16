//@ revisions: default certify certify_o holds
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[certify_o] compile-flags: -Ztrust-policy=certify -Copt-level=2
//@[holds] compile-flags: -Ztrust-policy=certify
//@[default] check-fail
//@[certify] check-fail
//@[certify_o] check-fail
//@[holds] check-pass
//@ dont-check-compiler-stderr
//! CAST-SIGNED-CLAMP-UB-1: a `min(v, C)` clamp on a SIGNED local is a bound on the
//! signed value, never on its unsigned image.
//!
//! `let l = if v > 10 { 10 } else { v }` with `v: i32` gives `l <= 10`, but `l` is
//! still unbounded below, and `l as usize` wraps `-1` to `usize::MAX`.
//! `trust_vcgen::generate::value_facts::unsigned_upper_bound` followed the cast into
//! the signed `l` with no signedness check: `l` has two definitions, so the
//! unstable-local path asked `clamp_upper_bound`, got 10, and
//! `build_additive_bound_facts` conjoined the GLOBAL fact `(l as usize) <= 10` into
//! every VC. Measured with `TRUST_FORMULA_DEBUG=1` on `c2_index` under certify
//! (BEFORE): the VC carries `(<= _5 10)` beside the correct wrap encoding of
//! `_5 = _6 as usize` (`_6 = copy l`),
//! `(=> (not (>= _6 0)) (= _5 (+ _6 18446744073709551616)))`, so the violation
//! `(>= _5 11)` is UNSAT. Beneath the cast, the Div arm carried the same signed bound
//! through `l / 2` (`m8_div`), and an `i8 -> u8` cast passed it on (`m3_i8`).
//!
//! BEFORE (`scratchpad/stage1-w15r`, main + wave 15, each revision's flags plus
//! `--cfg <rev> -Zui-testing -Zdeduplicate-diagnostics=no --emit=metadata -A unused`,
//! 2026-10-05): `default`, `certify` and `certify_o` each exit 1 with exactly the
//! two `ctl_oneblock` errors annotated below (the one-block spelling, already
//! caught: `0 proved, 1 failed`), and nothing else. Every liar reads `1 proved, 0
//! failed ... out of 1` (`m8_div`: `3 proved ... out of 3`), and in all three
//! revisions each liar's note adds `of which 1 kernel-certified by the clean CIC
//! kernel` (`m8_div`: 2). At run time `c2_index(-1)` panics "index out of bounds:
//! the len is 11 but the index is 18446744073709551615" and `c2_add(-1)` "attempt
//! to add with overflow" (`signed_clamp_cast_to_usize_keeps_bounds_check_run.rs`).
//! `holds` exits 0 with no diagnostic but the two controls' proved notes.
//!
//! AFTER (predicted before any stage 1 of the fix had run; it held,
//! MEASURED 2026-10-06 on the stage 1 of `9e11546767`): `unsigned_upper_bound` answers `None` for a signed component, so each
//! liar's cast keeps only its target type's range and its row is refuted, as
//! `ctl_oneblock`'s already is; each liar then draws the same two errors
//! `ctl_oneblock` draws today. `holds` is unchanged: the unsigned diamond and the
//! `Ord::clamp` lane (`callee_summaries::build_cast_bound_facts`, which requires a
//! non-negative lower bound) still prove. The crate-level evidence for the
//! prediction is `crates/trust-vcgen/tests/signed_clamp_cast_bound_realmir.rs`. It
//! runs these functions' real extracted MIR through `generate_vcs`, the in-process
//! ay and `trust_certify::certify_vc`: every liar row certified before the fix (and
//! ay-`Proved`, except `m8_div`'s bounds row, which ay left undecided), `Failed` and
//! uncertified after.

#[cfg(not(holds))]
pub fn c2_index(v: i32, arr: &[u8; 11]) -> u8 {
    //[default,certify,certify_o]~^ ERROR Trust Level 0 safety verification incomplete for `signed_clamp_cast_to_usize_keeps_bounds_check::c2_index`
    //[default,certify,certify_o]~^^ ERROR Trust strict verification failed for `signed_clamp_cast_to_usize_keeps_bounds_check::c2_index`
    let l = if v > 10 { 10 } else { v };
    arr[l as usize]
}

#[cfg(not(holds))]
pub fn c2_add(v: i32) -> u32 {
    //[default,certify,certify_o]~^ ERROR Trust Level 0 safety verification incomplete for `signed_clamp_cast_to_usize_keeps_bounds_check::c2_add`
    //[default,certify,certify_o]~^^ ERROR Trust strict verification failed for `signed_clamp_cast_to_usize_keeps_bounds_check::c2_add`
    let l = if v > 10 { 10 } else { v };
    (l as u32) + 4294967200
}

// The var arm on the TRUE edge.
#[cfg(not(holds))]
pub fn m2_lt(v: i32, arr: &[u8; 11]) -> u8 {
    //[default,certify,certify_o]~^ ERROR Trust Level 0 safety verification incomplete for `signed_clamp_cast_to_usize_keeps_bounds_check::m2_lt`
    //[default,certify,certify_o]~^^ ERROR Trust strict verification failed for `signed_clamp_cast_to_usize_keeps_bounds_check::m2_lt`
    let l = if v < 10 { v } else { 10 };
    arr[l as usize]
}

// Through an unsigned intermediate: `-1i8 as u8` is 255.
#[cfg(not(holds))]
pub fn m3_i8(v: i8, arr: &[u8; 11]) -> u8 {
    //[default,certify,certify_o]~^ ERROR Trust Level 0 safety verification incomplete for `signed_clamp_cast_to_usize_keeps_bounds_check::m3_i8`
    //[default,certify,certify_o]~^^ ERROR Trust strict verification failed for `signed_clamp_cast_to_usize_keeps_bounds_check::m3_i8`
    let l = if v > 10 { 10 } else { v };
    arr[(l as u8) as usize]
}

#[cfg(not(holds))]
pub fn m6_isize(v: isize, arr: &[u8; 11]) -> u8 {
    //[default,certify,certify_o]~^ ERROR Trust Level 0 safety verification incomplete for `signed_clamp_cast_to_usize_keeps_bounds_check::m6_isize`
    //[default,certify,certify_o]~^^ ERROR Trust strict verification failed for `signed_clamp_cast_to_usize_keeps_bounds_check::m6_isize`
    let l = if v >= 10 { 10 } else { v };
    arr[l as usize]
}

// Through the Div arm: `-3 / 2 == -1`.
#[cfg(not(holds))]
pub fn m8_div(v: i32, arr: &[u8; 11]) -> u8 {
    //[default,certify,certify_o]~^ ERROR Trust Level 0 safety verification incomplete for `signed_clamp_cast_to_usize_keeps_bounds_check::m8_div`
    //[default,certify,certify_o]~^^ ERROR Trust strict verification failed for `signed_clamp_cast_to_usize_keeps_bounds_check::m8_div`
    let l = if v > 10 { 10 } else { v };
    let d = l / 2;
    arr[d as usize]
}

// Already refused before the fix, and must stay refused.
#[cfg(not(holds))]
pub fn ctl_oneblock(v: i32, arr: &[u8; 11]) -> u8 {
    //[default,certify,certify_o]~^ ERROR Trust Level 0 safety verification incomplete for `signed_clamp_cast_to_usize_keeps_bounds_check::ctl_oneblock`
    //[default,certify,certify_o]~^^ ERROR Trust strict verification failed for `signed_clamp_cast_to_usize_keeps_bounds_check::ctl_oneblock`
    let mut l = v;
    if l > 10 {
        l = 10;
    }
    arr[l as usize]
}

// Controls, in every revision: genuinely in bounds, and proved before and after.
// The same diamond on an unsigned `v` keeps its bound.
pub fn ctl_u32(v: u32, arr: &[u8; 11]) -> u8 {
    let l = if v > 10 { 10 } else { v };
    arr[l as usize]
}

// `Ord::clamp` with a non-negative lower bound: a different lane, untouched.
pub fn ctl_ord_clamp(i: i32, arr: &[u8; 10]) -> u8 {
    let j = i.clamp(0, 9);
    arr[j as usize]
}
