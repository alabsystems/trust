#![crate_type = "lib"]
// MUTANT (self-limiting guard): the array size `4` -> `1000`. Now the reduction can
// reach `1000 * 255 = 255000`, which EXCEEDS u16::MAX (65535) — the accumulator
// overflows. The bound `t <= 1000*255` does NOT discharge `t + 255 <= 65535`, so the
// obligation stays SAT and the verifier MUST fail closed (exit 1). Guards that the
// accumulator bound uses the ACTUAL array length (a model ignoring N would falsely
// prove this real overflow).
pub fn bounded_array_reduction(a: &[u8; 1000]) -> u16 {
    let mut t: u16 = 0;
    for &x in a {
        t += x as u16;
    }
    t
}
