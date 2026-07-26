#![crate_type = "lib"]
// MUTANT (shift-reduction soundness twin): `t += (x as u8) << 4` over `[u8;64]` with a
// `u8` accumulator GENUINELY OVERFLOWS (`64 * (some x<<4)` exceeds 255). The post-add
// sum bound `K*per_max` exceeds u8::MAX, so the structural arithmetic discharge does NOT
// fire — the overflow stays refutable. `-full` MUST refute (exit 1). Pins that the
// bounded-reduction overflow discharge is SELF-LIMITING (proves only when the sum
// provably fits).
pub fn f(a: &[u8; 64]) -> u8 {
    let mut t: u8 = 0;
    for &x in a {
        t += (x as u8) << 4;
    }
    t
}
