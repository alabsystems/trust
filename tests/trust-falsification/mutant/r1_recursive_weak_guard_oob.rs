// TRAP: the recursive call increments i but the guard `i < 4` does NOT keep i+1 < 4 —
// off-by-one, i can reach 3, recurse to 4 -> OOB. P = i < 4 is NOT preserved.
fn walk(a: &[u32; 4], n: usize, i: usize) -> u32 {
    let x = a[i];
    if n > 0 && i < 4 { walk(a, n - 1, i + 1) } else { x }
}
pub fn go() -> u32 { walk(&[1, 2, 3, 4], 2, 0) }
