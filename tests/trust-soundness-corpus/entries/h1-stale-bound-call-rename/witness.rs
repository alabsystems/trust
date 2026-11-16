// trust-soundness-corpus entry `h1-stale-bound-call-rename` (H1 (STALE-BOUND-CALL-RENAME)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{:?}", src::pb04_folded_ref_bound_bug(&[0u8; 8], std::hint::black_box(100), 3));
}
