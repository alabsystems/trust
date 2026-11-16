// trust-soundness-corpus entry `trip-mid-test` (TRIP-MID-TEST-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{}", src::mid_wrap());
}
