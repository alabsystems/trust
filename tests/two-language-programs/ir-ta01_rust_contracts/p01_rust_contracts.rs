// FEATURE rust.contracts — requires / ensures / decreases in the compiler grammar.
// EXPECT: 49
#[inline(never)]
pub fn clamp_add(x: u64, y: u64) -> u64
    requires x <= 1000
    requires y <= 1000
    ensures result == x + y
{
    x + y
}
#[inline(never)]
pub fn countdown(n: u64) -> u64
    decreases n
{
    if n > 0 { countdown(n - 1) } else { 7 }
}
pub fn program() -> u64 {
    clamp_add(40, 2) + countdown(5)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
