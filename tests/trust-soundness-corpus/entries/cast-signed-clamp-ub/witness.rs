// trust-soundness-corpus entry `cast-signed-clamp-ub` (CAST-SIGNED-CLAMP-UB-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    let v = std::hint::black_box(-1i32);
    println!("{}", src::c2_index(v, &[7u8; 11]));
}
