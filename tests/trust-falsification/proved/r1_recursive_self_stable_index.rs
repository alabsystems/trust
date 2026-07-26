// WIN: self-recursion. n (1st int arg) decreases -> terminates; i held constant,
// invariant P = i < 4 is inductive (recursive arg == i). Base case: go() calls walk(_,3,2).
fn walk(a: &[u32; 4], n: usize, i: usize) -> u32 {
    let x = a[i];
    if n > 0 { walk(a, n - 1, i) } else { x }
}
pub fn go() -> u32 { walk(&[1, 2, 3, 4], 3, 2) }
