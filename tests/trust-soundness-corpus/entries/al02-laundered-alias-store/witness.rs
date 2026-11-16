// trust-soundness-corpus entry `al02-laundered-alias-store` (al02 (LAUNDERED-ALIAS-STORE)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{:?}", src::al02_launder_store_read_bug(&[0u8; 8], std::hint::black_box(100), 3));
}
