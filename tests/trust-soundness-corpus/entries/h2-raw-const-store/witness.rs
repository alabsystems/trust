// trust-soundness-corpus entry `h2-raw-const-store` (H2 (RAW-CONST-STORE)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{:?}", src::ce06_raw_const_store_index_bug(std::hint::black_box(0), &[0u8; 4]));
}
