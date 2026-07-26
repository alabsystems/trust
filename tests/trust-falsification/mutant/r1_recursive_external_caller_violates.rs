// TRAP: `rec` holds i constant (P = i < 4 IS inductive internally), but the external
// caller `bad_entry` calls rec(_, _, 9) — 9 >= 4, so the base case FAILS. Must reject.
fn rec(a: &[u32; 4], n: usize, i: usize) -> u32 {
    let x = a[i];
    if n > 0 { rec(a, n - 1, i) } else { x }
}
pub fn bad_entry() -> u32 { rec(&[1, 2, 3, 4], 3, 9) }
