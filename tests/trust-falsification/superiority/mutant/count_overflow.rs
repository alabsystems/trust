#![crate_type = "lib"]
// SOUNDNESS discriminator for the constant-addend (counter) accumulator bound (#50). The
// loop runs 100_000 times each adding 1, so the u16 accumulator genuinely overflows
// (100_000 > u16::MAX = 65535). The bound `t <= 100_000` IS emitted (the trip count is the
// constant range length), but it is self-limiting: 100_000 exceeds u16::MAX, so the
// per-iteration overflow obligation stays SAT and the runtime check is correctly retained.
// Proves the counter bound is non-vacuous.
pub fn count_overflow() -> u16 {
    let mut t: u16 = 0;
    for _ in 0..100_000 {
        t += 1;
    }
    t
}
