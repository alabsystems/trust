// trust-soundness-corpus entry `wp-d237-shadowed-namesake` (trust-wp D-237 (rs1)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
use std::rc::Rc;
fn main() {
    let r = Rc::new(1i32);
    let r2 = r.clone();
    let r = Rc::new(std::hint::black_box(2i32));
    println!("r = {r}, r2 = {r2}");
    assert!(r == r2, "proof_assert!(r == r2) is false");
}
