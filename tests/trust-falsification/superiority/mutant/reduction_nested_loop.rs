#![crate_type = "lib"]
// MUTANT (single-loop soundness guard): a NESTED loop multiplies the trip count, so
// `t` accumulates 4*1000 elements, not 4 — `t` can reach `4000 * 255 = 1.02e6` >>
// u16::MAX. The accumulator-bound recognizer requires EXACTLY ONE loop
// (count_back_edges == 1); with a nested loop it emits NO bound, so the unbounded `t`
// overflow stays SAT and the verifier MUST fail closed. Guards that the bound is never
// applied when the self-add runs more than N times.
pub fn reduction_nested_loop(a: &[u8; 4]) -> u16 {
    let mut t: u16 = 0;
    for &x in a {
        for _ in 0..1000 {
            t += x as u16;
        }
    }
    t
}
