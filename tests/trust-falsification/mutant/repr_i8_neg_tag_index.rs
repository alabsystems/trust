#![crate_type = "lib"]
// NEGATIVE ENUM DISCRIMINANT AS AN INDEX. `#[repr(i8)] E { A = -1, B = 2 }` and
// `t[e as usize]`. IT FAULTS: `E::A as usize` is 18446744073709551615 (measured,
// not asserted — the oracle prints the cast), so the index is out of bounds for
// any array and the body panics.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 1 panic / 2 runs, sweep = both
// variants of `E` (the whole input domain of `e`), `A` panicking and `B` not.
//
// THE ARRAY IS `[u32; 300]` ON PURPOSE, AND THE LENGTH IS LOAD-BEARING. With a
// raw (unsign-extended) `i8` tag the extracted discriminant of `A` is 255. On a
// SHORT array the verifier then refutes `t[255]` BY ACCIDENT of the length — the
// tag decode is never exercised. Measured: the same body over `[u32; 4]`
// answers `refuted` on pristine `70a7534fd1` AND on `campaign-integration`, so
// it discriminates nothing. At length 300 the raw tag 255 is IN BOUNDS, the
// undecoded index proves, and the fixture actually tests the decode.
//
// Two-column measurement, `-Ztrust-policy=certify`: pristine `70a7534fd1`
// answers `proved` (SURVIVING MUTANT); `campaign-integration` answers
// `refuted`. The fixture discriminates.
#[repr(i8)]
pub enum E {
    A = -1,
    B = 2,
}
pub fn repr_i8_neg_tag_index(e: E, t: &[u32; 300]) -> u32 {
    t[e as usize]
}
