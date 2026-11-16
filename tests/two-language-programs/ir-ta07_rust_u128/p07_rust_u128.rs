// FEATURE rust.u128 — 128-bit arithmetic with a constant above i128::MAX.
// EXPECT: 2
#[inline(never)]
pub fn wide(a: u64, b: u64) -> u64 {
    let big: u128 = 0xFFFF_FFFF_0000_0000_0000_0000_0000_0000;
    let p = ((a as u128) * (b as u128)) ^ big;
    ((p >> 64) as u64) ^ (p as u64)
}
pub fn program() -> u64 {
    wide(0x1_0000_0001, 0x1_0000_0003) & 0xFFFF
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
