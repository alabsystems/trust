// trust-soundness-corpus entry `trip-init-cycle` (TRIP-INIT-CYCLE-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{}", src::reset_loop(std::hint::black_box(0)));
}
