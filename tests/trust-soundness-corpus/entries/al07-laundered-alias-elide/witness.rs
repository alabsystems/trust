// trust-soundness-corpus entry `al07-laundered-alias-elide` (LAUNDERED-ALIAS-ELIDE-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{:?}", src::al07_cast_store_add_bug(std::hint::black_box(usize::MAX), 3));
}
