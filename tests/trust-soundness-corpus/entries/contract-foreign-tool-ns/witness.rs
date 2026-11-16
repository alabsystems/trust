// trust-soundness-corpus entry `contract-foreign-tool-ns` (CONTRACT-NS-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{}", src::f(std::hint::black_box(300)));
}
