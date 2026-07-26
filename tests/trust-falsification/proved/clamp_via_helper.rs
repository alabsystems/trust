#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): `arr[clamp_idx(i)]` where the helper
// `clamp_idx` returns `i.min(LEN - 1)` now proves. A whole-crate return-bound
// SUMMARY (computed once at the analysis phase) records `clamp_idx <= 7`; the
// call site then emits the SSA-gated, staleness-versioned fact `dest <= 7`,
// which discharges the length-8 index `dest < 8`. SOUND: the summary is
// const-certain + single-assigned + non-negative, and a `&mut` reassignment of
// the call result drops the bound (same defense as the stdlib min/max/clamp
// call bounds). Safe ⇒ no Failed obligation ⇒ `-full` exits 0.
fn clamp_idx(i: usize) -> usize {
    i.min(7)
}

pub fn f(arr: &[u8; 8], i: usize) -> u8 {
    arr[clamp_idx(i)]
}
