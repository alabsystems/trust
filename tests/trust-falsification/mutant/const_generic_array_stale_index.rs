#![crate_type = "lib"]
// Trust: piece #7a (INV-3) — reassign `i` after the guard; the proved bound is
// STALE, so `a[i]` with i=usize::MAX is OOB. MUST refute (index-versioning net).
pub fn cg_stale_index<const N: usize>(a: [u8; N], mut i: usize) -> u8 {
    if i < N { i = usize::MAX; a[i] } else { 0 }
}
