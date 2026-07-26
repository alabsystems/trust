#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): `arr[n.trailing_zeros() as usize]` proves under BOTH
// modes. `-full` was native-blocked ("Call target ...trailing_zeros is not present in the TrustIr
// module"); the native bridge now models the unconditionally-total bit-count intrinsics as a fresh
// symbolic result CONSTRAINED by `Inst::Assume(result <= width)`. trailing_zeros(u32) is in [0,32],
// so a length-33 array (covering tz(0)==32) is in bounds.
pub fn f(n: u32, arr: &[u8; 33]) -> u8 {
    arr[n.trailing_zeros() as usize]
}
