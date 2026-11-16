// trust-soundness-corpus entry `trip-driver` (TRIP-DRIVER-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{}", src::stray_on_cycle(std::hint::black_box(0)));
}
