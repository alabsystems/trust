// trust-soundness-corpus entry `union-sibling-write` (UNION-SIBLING-WRITE-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    println!("{:?}", src::u_dst_add(std::hint::black_box(0)));
}
