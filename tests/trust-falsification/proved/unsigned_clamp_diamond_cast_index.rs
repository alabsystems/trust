#![crate_type = "lib"]
// COMPLETENESS (CAST-SIGNED-CLAMP-UB-1 control): `l = if v > 10 { 10 } else { v }` on an
// UNSIGNED `v` is `min(v, 10)`, in `[0, 10]`, so `l as usize < 11` and the access is in
// bounds. `l` has two definitions (the diamond's arms), so the bound comes from
// `value_facts::clamp_upper_bound` through `unsigned_upper_bound`'s cast arm. The fix keeps
// that lane for unsigned sources; its signed twin is mutant/signed_clamp_cast_index_oob.rs.
pub fn f(v: u32, arr: &[u8; 11]) -> u8 {
    let l = if v > 10 { 10 } else { v };
    arr[l as usize]
}
