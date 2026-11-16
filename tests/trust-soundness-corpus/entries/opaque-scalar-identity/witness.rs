// trust-soundness-corpus entry `opaque-scalar-identity` (B (OPAQUE-SCALAR-ID-1)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    let (a, b) = (1u8, 2u8);
    println!("{}", src::cc_two_addrs(&a, &b));
}
