// DIRECTION 2 — a genuine refutation. `a + b` on u32 overflows for reachable
// inputs; the verifier finds the counterexample. This fails under EVERY policy,
// including the default. Policy B tolerates gaps, never refutations.
pub fn add(a: u32, b: u32) -> u32 {
    a + b
}
