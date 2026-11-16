// trust-soundness-corpus entry `vac-field-read-before-write` (vac). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
// The postcondition `result && !result` is false for every result; the witness
// evaluates it on the value the body returns.
#![allow(unused_mut)]
pub struct S {
    pub f: bool,
}
pub fn vac(mut s: S) -> bool {
    s.f = !s.f;
    s.f
}
fn main() {
    let result = vac(S { f: std::hint::black_box(false) });
    println!("result = {result}; postcondition result && !result = {}", result && !result);
    assert!(result && !result, "postcondition violated");
}
