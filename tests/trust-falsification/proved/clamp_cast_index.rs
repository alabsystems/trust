#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): `let j = i.clamp(lo, hi); arr[j as usize]`. The clamp
// emits `lo <= j <= hi`, but the index is `j as usize` — a SEPARATE local the clamp bound never
// reaches (ay does not model the signed→unsigned cast as an equality). For const `0 <= lo <= hi`,
// `j as uN = j mod 2^N <= hi` holds unconditionally, so `build_clamp_cast_facts` emits
// `(j as usize) <= hi`, discharging the access when `hi < arr.len()`.
pub fn f(i: i32, arr: &[u8; 10]) -> u8 {
    let j = i.clamp(0, 9);
    arr[j as usize]
}

// Non-zero lower bound: `j ∈ [2, 7] ⊂ [0, 8)`.
pub fn g(i: i32, arr: &[u8; 8]) -> u8 {
    let j = i.clamp(2, 7);
    arr[j as usize]
}
