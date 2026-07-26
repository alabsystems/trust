#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): a value-bounded bit-count intrinsic used as
// an index is in bounds — `arr[n.count_ones() as usize]` / `trailing_zeros()` /
// `leading_zeros()` over `[_; bits(T)+1]` (the count is in `[0, bits(T)]`). These are
// unconditionally-true LINEAR bounds (`build_intrinsic_bound_facts`) that ay discharges;
// the unsigned bit-count → usize cast is value-preserving, so the bound reaches the index.
// (`rem_euclid` gets the same bound in default mode but its native TrustIr lowering is a
// separate gap, so it is not in this -full fixture.)
pub fn count_idx(n: u8) -> u8 { let arr = [0u8; 9]; arr[n.count_ones() as usize] }
pub fn tz_idx(n: u8) -> u8 { let arr = [0u8; 9]; arr[n.trailing_zeros() as usize] }
pub fn lz_idx(n: u32) -> u8 { let arr = [0u8; 33]; arr[n.leading_zeros() as usize] }
