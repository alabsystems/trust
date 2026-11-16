// FEATURE rust.std_call — a call into `core` (an UPSTREAM body: is it carried, or a placeholder?).
// EXPECT: 5
#[inline(never)]
pub fn wrap_inc(x: u64) -> u64 {
    x.wrapping_add(1)
}
pub fn program() -> u64 {
    wrap_inc(u64::MAX) + wrap_inc(4)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
