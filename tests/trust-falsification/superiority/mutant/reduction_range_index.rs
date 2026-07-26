#![crate_type = "lib"]
// MUTANT (wrong-collection-link soundness guard): a RANGE loop indexes the array
// `a[i % 4]` 1000 times — the trip count is 1000, NOT the array length 4. The
// accumulator's addend comes from an INDEX expression, not a for-each over `a`, so the
// recognizer does NOT link it to `a`'s length and emits no bound; `t` can reach
// `1000 * 255 = 255000` > u16::MAX, so the overflow stays SAT and the verifier MUST
// fail closed. Guards against linking the accumulator to the wrong collection's length.
pub fn reduction_range_index(a: &[u8; 4]) -> u16 {
    let mut t: u16 = 0;
    for i in 0..1000usize {
        t += a[i % 4] as u16;
    }
    t
}
