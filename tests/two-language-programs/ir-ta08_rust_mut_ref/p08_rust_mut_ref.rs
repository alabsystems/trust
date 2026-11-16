// FEATURE rust.mut_ref — a `&mut` function (the give-back shape).
// EXPECT: 21
#[inline(never)]
pub fn bump(x: &mut u64, by: u64) {
    *x = *x + by;
}
pub fn program() -> u64 {
    let mut v = 10u64;
    bump(&mut v, 5);
    bump(&mut v, 6);
    v
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
