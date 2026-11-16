// trust-soundness-corpus entry `h3-asm-output` (H3 (OPAQUE-ASM-OUTPUT)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{:?}", src::h3a_out_bug(std::hint::black_box(0), &[0u8; 4]));
}
