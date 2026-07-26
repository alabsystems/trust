#![crate_type = "lib"]
// PROVED (-full StepBy<Range> EXCLUSIVE-bound pivot): `for i in (0..8).step_by(1)`
// over a `[u8; 8]` yields i in {0, 1, …, 7} — EVERY yield is `< 8`, and the
// largest yield 7 is the LAST valid index, so `arr[i]` is always in bounds while
// `arr[8]` is NEVER reached. This is the load-bearing proof of the EXCLUSIVE upper
// bound: the native model asserts `v < 8` (Ult), not `v <= 8` (Ule). With the OLD
// hard-coded inclusive `<=` (the red-team finding), `v == 8` would be admitted and
// an `arr[8]` access would false-prove; with the exclusive `<` it is correctly
// excluded. Verifies (exit 0) — and its off-by-one twin `step_by_excl_off_by_one`
// in mutant/ REFUTES, pinning the bound's tightness.
pub fn f(arr: &[u8; 8]) -> u8 {
    let mut s = 0u8;
    for i in (0..8).step_by(1) {
        s ^= arr[i];
    }
    s
}
