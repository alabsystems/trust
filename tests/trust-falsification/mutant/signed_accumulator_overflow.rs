#![crate_type = "lib"]
// MUTANT (signed-accumulator soundness twin): summing `[i8; 8]` elements INTO AN i8
// accumulator GENUINELY OVERFLOWS — eight elements up to 127 each sum to 1016 > i8::MAX
// (127). No widening cast feeds the add, so no symmetric reduction bound is synthesized
// and the accumulator stays unconstrained; `-full` MUST refute the per-add overflow
// (exit 1). Pins that the signed reduction discharge is SELF-LIMITING: it fires only when
// the `[C + K*MIN, C + K*MAX]` endpoints fit the accumulator type.
pub fn f(a: &[i8; 8]) -> i8 {
    let mut s: i8 = 0;
    for &x in a {
        s += x;
    }
    s
}
