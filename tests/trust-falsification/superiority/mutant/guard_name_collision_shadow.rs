#![crate_type = "lib"]
// SOUNDNESS REGRESSION (name-collision false proof, found by the adversarial false-proof
// hunt). The dominating guard `a <= 1000` bounds the OUTER parameter `a`, but `let a = b`
// shadows it with a DISTINCT local that aliases the unbounded `b`. If the BV-mul
// dominating-guard constraint were matched to the multiply operands by the non-unique
// source name "a" (the bug), the interval backend would see `a*a` with both operands
// `<= 1000` and prove no overflow — a FALSE PROOF (b can be 99999, 99999*99999 overflows
// u32). place_to_var_name now disambiguates the two `a` locals, so the guard cannot attach
// to the shadow's operands: this stays NOT fully discharged (the `a*a` is correctly
// retained).
pub fn f(a: u32, b: u32) -> u32 {
    if a <= 1000 {
        let a = b;
        a * a
    } else {
        0
    }
}
