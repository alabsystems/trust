// trust-soundness-corpus entry `path-guard-value-range` (A' (range twin of A)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    let r = src::g01_range_bug(&[true], &[0u8; 8], 3, std::hint::black_box(100));
    println!("{r}");
}
