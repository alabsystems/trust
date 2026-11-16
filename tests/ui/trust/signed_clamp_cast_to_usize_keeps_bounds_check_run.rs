//@ revisions: idx add
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@[idx] error-pattern: index out of bounds: the len is 11 but the index is 18446744073709551615
//@[add] error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The run twin of `signed_clamp_cast_to_usize_keeps_bounds_check.rs`
//! (CAST-SIGNED-CLAMP-UB-1): the programs whose rows the verifier certified.
//! `l = if v > 10 { 10 } else { v }` leaves `l` unbounded below, so `v = -1`
//! makes `l as usize` `usize::MAX` and `l as u32` `u32::MAX`.
//!
//! The lie was a false row, not a removed check: a verifying build keeps the
//! panic, so this twin is built with verification OFF and shows what the
//! certified claims are claims about. Measured 2026-10-05 on
//! `scratchpad/stage1-w15r` (main + wave 15) with exactly these flags (plus
//! `--cfg <rev> -A unused`): `idx` builds exit 0 and runs exit 101 with "index out
//! of bounds: the len is 11 but the index is 18446744073709551615"; `add` builds
//! exit 0 and runs exit 101 with "attempt to add with overflow". The same `idx`
//! source built with `-Ztrust-verify=on` (default policy) and `TRUST_ELIDE_DEBUG=1`
//! also exits 0, prints `elided 0 kernel-certified overflow checks` for `c2_index`,
//! `c2_add` and `main`, and its run panics the same way. The fix does not touch
//! the verify-off build, so both revisions are unchanged after it.

#[inline(never)]
pub fn c2_index(v: i32, arr: &[u8; 11]) -> u8 {
    let l = if v > 10 { 10 } else { v };
    arr[l as usize]
}

#[inline(never)]
pub fn c2_add(v: i32) -> u32 {
    let l = if v > 10 { 10 } else { v };
    (l as u32) + 4294967200
}

fn main() {
    let v = std::hint::black_box(-1i32);
    let arr = [7u8; 11];
    #[cfg(idx)]
    let _ = std::hint::black_box(c2_index(v, &arr));
    #[cfg(add)]
    let _ = std::hint::black_box(c2_add(v));
    let _ = (v, arr);
}
