// Rust calls a genuinely recursive, well-founded Clean definition over `Nat`
// (fuelled subtractive Euclid), emitted and gate-verified by the compiler.
extern crate trust_bignum;
clean {
    def gcdF (f a b : Nat) : Nat := if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a
    termination_by f
}
fn nat(v: u64) -> trust_bignum::Nat { trust_bignum::Nat::from_u64(v) }
fn gcd(a: u64, b: u64) -> u64 {
    gcdF(nat(a + 2 * b), nat(a), nat(b)).to_u64().expect("fits")
}
fn main() {
    for (a, b, e) in [(12u64, 18u64, 6u64), (270, 192, 6), (7, 13, 1), (0, 5, 5), (5, 0, 5)] {
        assert_eq!(gcd(a, b), e);
    }
    println!("gcd(270,192) = {}", gcd(270, 192));
}
