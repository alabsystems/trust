// FEATURE lean.nat_structural — structural recursion over Nat (the Nat-handle lane).
// EXPECT: 11
extern crate trust_bignum;
clean {
    def tozero : Nat -> Nat
      | 0 => 0
      | n + 1 => tozero n
}
pub fn program() -> u64 {
    let out = tozero(trust_bignum::Nat::from_u64(3));
    match out.to_u64() { Some(v) => v + 11, None => 0 }
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
