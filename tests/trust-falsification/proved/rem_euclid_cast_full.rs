#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): `arr[n.rem_euclid(6) as usize]` (signed n) now proves
// under BOTH modes. `-full` was native-blocked on the rem_euclid call; the native bridge now models
// a CONST-divisor rem_euclid as total with `Inst::Assume(0 <= result <= |c|-1)`. rem_euclid(6) is in
// [0,5] for any sign of n, so a length-6 array is in bounds. The lower `0 <= result` assume matters
// because the i32 result type would otherwise admit negatives the `as usize` cast wraps huge.
pub fn f(n: i32, arr: &[u8; 6]) -> u8 {
    arr[n.rem_euclid(6) as usize]
}
