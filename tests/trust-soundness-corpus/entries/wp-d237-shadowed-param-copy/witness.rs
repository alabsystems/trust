// trust-soundness-corpus entry `wp-d237-shadowed-param-copy` (trust-wp D-237 (pa2)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
fn pa2(x: i32) {
    assert!(x > 0 && x < 100, "requires");
    let y = x;
    let x = 0i32;
    println!("y = {y}, x = {x}");
    assert!(y == x, "proof_assert!(y == x) is false");
}
fn main() {
    pa2(std::hint::black_box(5));
}
