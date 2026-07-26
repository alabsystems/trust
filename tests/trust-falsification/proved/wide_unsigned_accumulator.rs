#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): a bounded reduction into a WIDE unsigned
// accumulator (u64/u128). `t += x as u64` / `t += (x as u128) << 4` over a fixed array
// is bounded (`t <= N*per_max << MAX(u64/u128)`), but the per-add overflow threshold is
// `UInt(u64::MAX)` / `UInt(u128::MAX)` — which EXCEEDS i128::MAX, so the structural
// arithmetic discharge could not read it. Fixed by handling a `UInt` upper bound in the
// `Gt` arm (`le_threshold`). The genuinely-overflowing `[u128;N]`-element reduction stays
// runtime-checked (its per-element bound is u128::MAX → the sum overflows).
pub fn u64_acc(a: &[u8; 64]) -> u64 { let mut t: u64 = 0; for &x in a { t += x as u64; } t }
pub fn u128_shift(a: &[u8; 16]) -> u128 { let mut t: u128 = 0; for &x in a { t += (x as u128) << 4; } t }
