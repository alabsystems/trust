// trust-soundness-corpus entry `path-guard-value` (A (PATH-GUARD-VALUE-1)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    let r = src::gs_one_arm_scalar_bug(&[true], &[0u8; 8], 3, std::hint::black_box(100));
    println!("{r}");
}
