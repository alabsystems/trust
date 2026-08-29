#![crate_type = "lib"]
// QUARANTINED — OVER-REFUTATION, LIVE ON BOTH COLUMNS. `(c as u32) + 1` for a
// `char`. IT DOES NOT FAULT: `char` is a Unicode scalar value, so `c as u32` is
// at most 0x10FFFF and the addition cannot overflow a `u32`.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 1112064 runs, sweep =
// EVERY char in the language (0..=0xD7FF and 0xE000..=0x10FFFF). The sweep is
// exhaustive, not sampled: there is no input at which this function panics.
//
// Measured under `-Ztrust-policy=certify`: pristine `70a7534fd1` answers
// `refuted` and `campaign-integration` ALSO answers `refuted`, both with
// `Level 0 summary: 1 failed` on the `[overflow:add]`. This is not a decline and
// not an unknown — it is a definite wrong answer about a function that is total
// over its whole input domain, so the `char`-to-integer cast is publishing no
// value relation that bounds the result by the scalar-value range.
//
// It stays OUT of the gated `proved/` lane only because landing it there would
// make the gate red for a defect that is already recorded here with a
// reproducer. Move it to `proved/` the moment it verifies.
pub fn char_cast_increment(c: char) -> u32 {
    (c as u32) + 1
}
