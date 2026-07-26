#![crate_type = "lib"]
// MUTANT of superiority/proved/min_three.rs: drops `c.len()` from the min, so the
// loop bound `n = min(a.len(), b.len())` does NOT bound `c`. `c[i]` is OUT OF
// BOUNDS whenever `c` is shorter than `min(a, b)`, so default mode must NOT
// eliminate the `c[i]` check.
pub fn min_three(a: &[u8], b: &[u8], c: &[u8]) -> u8 {
    let n = a.len().min(b.len());
    let mut t = 0u8;
    for i in 0..n {
        t ^= a[i] ^ b[i] ^ c[i];
    }
    t
}
