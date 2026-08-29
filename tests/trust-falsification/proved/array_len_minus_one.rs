#![crate_type = "lib"]
// FALSE-REFUTATION GUARD: `a.len() - 1` on a `&[u8; 8]`. `len()` on an array
// reference goes through the array-to-slice unsize coercion. IT DOES NOT FAULT:
// the length is the constant 8, so the subtraction is 7 and cannot underflow.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 1 run — the body takes no
// input beyond the array reference, so one run IS the whole input domain.
//
// WHY IT IS A GATE FIXTURE. If the unsize coercion discards the array length,
// the derived slice length becomes a free variable and the solver picks 0, so a
// total function is reported as an underflow.
//
// Two-column measurement, `-Ztrust-policy=certify`: pristine `70a7534fd1`
// answers `refuted` with `[overflow:sub] FAILED ... _3__slice_len = 0` — a
// length the array cannot have. `campaign-integration` answers `proved`. The
// fixture discriminates.
pub fn array_len_minus_one(a: &[u8; 8]) -> usize {
    a.len() - 1
}
