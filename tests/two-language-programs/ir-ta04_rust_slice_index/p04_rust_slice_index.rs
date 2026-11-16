// FEATURE rust.slice_index — slice indexing, which carries a bounds obligation.
// EXPECT: 8
#[inline(never)]
pub fn nth(xs: &[u64], i: usize) -> u64
    requires i < xs.len()
{
    xs[i]
}
pub fn program() -> u64 {
    let arr = [7u64, 8, 9];
    nth(&arr, 1)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
