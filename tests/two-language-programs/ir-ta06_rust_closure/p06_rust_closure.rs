// FEATURE rust.closure — a capturing closure, called twice.
// EXPECT: 11
#[inline(never)]
pub fn apply_twice(k: u64, x: u64) -> u64 {
    let add_k = |v: u64| v + k;
    add_k(add_k(x))
}
pub fn program() -> u64 {
    apply_twice(5, 1)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
