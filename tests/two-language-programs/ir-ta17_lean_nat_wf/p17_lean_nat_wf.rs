// FEATURE lean.nat_wf — well-founded recursion over Nat (termination_by).
// EXPECT: 15
extern crate trust_bignum;
clean {
    def countdownSum (n : Nat) : Nat := if h : 0 < n then n + countdownSum (n - 1) else 0
    termination_by n
}
pub fn program() -> u64 {
    let out = countdownSum(trust_bignum::Nat::from_u64(5));
    match out.to_u64() { Some(v) => v, None => 0 }
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
