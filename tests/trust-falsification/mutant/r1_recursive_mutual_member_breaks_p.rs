// TRAP: 2-member mutual recursion. ping holds i constant, but pong recurses to ping
// with i+1 UNGUARDED -> the SCC's P = i < 8 is NOT jointly inductive. Must reject.
fn ping(a: &[u32; 8], n: usize, i: usize) -> u32 {
    let x = a[i];
    if n > 0 { pong(a, n - 1, i) } else { x }
}
fn pong(a: &[u32; 8], n: usize, i: usize) -> u32 {
    let y = a[i];
    if n > 0 { ping(a, n - 1, i + 1) } else { y }
}
pub fn go() -> u32 { ping(&[0u32; 8], 5, 0) }
