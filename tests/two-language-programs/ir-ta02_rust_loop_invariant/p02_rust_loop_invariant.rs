// FEATURE rust.loop_invariant — `invariant` + `decreases` on a while loop.
// EXPECT: 45
#[inline(never)]
pub fn sum_below(n: u64) -> u64
    requires n <= 1000
{
    let mut i = 0u64;
    let mut s = 0u64;
    while i < n
        invariant i <= n
        decreases n - i
    {
        s = s + i;
        i += 1;
    }
    s
}
pub fn program() -> u64 {
    sum_below(10)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
