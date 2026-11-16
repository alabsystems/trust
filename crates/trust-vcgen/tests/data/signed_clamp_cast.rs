// Source for the `signed_clamp_cast_<fn>.json` fixtures (CAST-SIGNED-CLAMP-UB-1).
//
// Captured with the stage 1 of main + wave 15 (before the fix), from a file named
// `signed_clamp.rs` (so each `def_path` is `signed_clamp::<fn>`):
//   trustc --edition 2021 --crate-type lib -Ztrust-verify=on \
//          -Ztrust-dump=mir:<dir> --emit=metadata signed_clamp.rs -o /dev/null
//
// Every `l` below is a SIGNED min-clamp, so `l` can be negative and `l as usize`
// (or `l as u32`) wraps it to a huge value: each liar's row is FALSE. `ctl_u32`
// is the same clamp on an unsigned `v` and is genuinely in bounds. `ctl_oneblock`
// is a one-block spelling of `c2_index` that the verifier already refused.
pub fn c2_index(v: i32, arr: &[u8; 11]) -> u8 { let l = if v > 10 { 10 } else { v }; arr[l as usize] }
pub fn c2_add(v: i32) -> u32 { let l = if v > 10 { 10 } else { v }; (l as u32) + 4294967200 }
pub fn m2_lt(v: i32, arr: &[u8; 11]) -> u8 { let l = if v < 10 { v } else { 10 }; arr[l as usize] }
pub fn m3_i8(v: i8, arr: &[u8; 11]) -> u8 { let l = if v > 10 { 10 } else { v }; arr[(l as u8) as usize] }
pub fn m6_isize(v: isize, arr: &[u8; 11]) -> u8 { let l = if v >= 10 { 10 } else { v }; arr[l as usize] }
pub fn m8_div(v: i32, arr: &[u8; 11]) -> u8 { let l = if v > 10 { 10 } else { v }; let d = l / 2; arr[d as usize] }
pub fn ctl_u32(v: u32, arr: &[u8; 11]) -> u8 { let l = if v > 10 { 10 } else { v }; arr[l as usize] }
pub fn ctl_oneblock(v: i32, arr: &[u8; 11]) -> u8 { let mut l = v; if l > 10 { l = 10; } arr[l as usize] }
