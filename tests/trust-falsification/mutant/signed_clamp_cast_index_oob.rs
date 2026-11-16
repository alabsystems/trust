#![crate_type = "lib"]
// MUTANT (CAST-SIGNED-CLAMP-UB-1): `l = if v > 10 { 10 } else { v }` is a min-clamp on a
// SIGNED `v`, so `l` is still unbounded BELOW. `l as usize` wraps a negative `l` to a huge
// index (`v = -1` indexes 18446744073709551615), so this access genuinely panics and the
// bounds row MUST be refuted (exit 1). The clamp's `l <= 10` is a bound on the signed value,
// never on its unsigned image; publishing it as `(l as usize) <= 10` false-proved this row
// Certified (clean kernel) before the fix. Its unsigned twin, which must keep proving, is
// proved/unsigned_clamp_diamond_cast_index.rs.
pub fn f(v: i32, arr: &[u8; 11]) -> u8 {
    let l = if v > 10 { 10 } else { v };
    arr[l as usize]
}
