// TRAP: recursion increments the index i each call with NO guard keeping i < len.
// P = i < 4 is NOT inductive (recursive arg i+1 can exceed the bound). Genuinely OOB.
fn bad(a: &[u32; 4], n: usize, i: usize) -> u32 {
    let x = a[i];
    if n > 0 { bad(a, n - 1, i + 1) } else { x }
}
pub fn go() -> u32 { bad(&[1, 2, 3, 4], 10, 0) }
