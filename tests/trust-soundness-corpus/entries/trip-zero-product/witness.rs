// trust-soundness-corpus entry `trip-zero-product` (TRIP-ZERO-PRODUCT-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{}", src::count_after_warmup());
}
