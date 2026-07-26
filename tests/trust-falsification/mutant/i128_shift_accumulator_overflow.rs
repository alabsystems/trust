#![crate_type = "lib"]
// MUTANT (i128 reduction soundness twin): summing i128 ELEMENTS directly — four values up to
// i128::MAX GENUINELY OVERFLOW. The recognizer rejects signed-i128 elements (no bounded per-element
// max), so NO BV accumulator bound is rendered; `-full` MUST refute the per-add overflow (exit 1).
// Pins that the BV bound-render is SELF-LIMITING (an unbounded signed reduction stays refutable).
pub fn f(a: &[i128; 4]) -> i128 {
    let mut t: i128 = 0;
    for &x in a {
        t += x;
    }
    t
}
