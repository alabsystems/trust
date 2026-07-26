// WIN: 2-member mutual recursion (ping <-> pong), one SCC. Each holds index `i`
// constant; invariant P = `i < 8` is JOINTLY inductive across BOTH intra-SCC edges
// (ping->pong and pong->ping preserve i). `n` decreases -> terminates. Base case:
// go() calls ping(_, 5, 3), establishing 3 < 8. No arithmetic -> no overflow.
// `#[inline(never)]` breaks a pre-existing MIR-optimization query cycle that the
// inliner otherwise forms across the mutual pair (unrelated to R1).
#[inline(never)]
fn ping(a: &[u32; 8], n: usize, i: usize) -> u32 {
    let x = a[i];
    if n > 0 { pong(a, n - 1, i) } else { x }
}
#[inline(never)]
fn pong(a: &[u32; 8], n: usize, i: usize) -> u32 {
    let y = a[i];
    if n > 0 { ping(a, n - 1, i) } else { y }
}
pub fn go() -> u32 { ping(&[0u32; 8], 5, 3) }
