// FEATURE rust.checked_arith — `+`/`*`//` with overflow / div-by-zero obligations.
// EXPECT: 62
#[inline(never)]
pub fn scale(a: u32, b: u32) -> u32
    requires a <= 1000
    requires b <= 1000
{
    a * b + a
}
#[inline(never)]
pub fn ratio(a: u64, b: u64) -> u64 {
    if b == 0 { 0 } else { a / b }
}
pub fn program() -> u64 {
    scale(6, 7) as u64 + ratio(100, 7)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
