// NOT a correct refusal — a FALSE REFUTATION, and it was mislabelled here as the
// opposite until 2026-09-18.
//
// The head invariant is `c == i <= n`, so the body only ever runs with
// `c <= n - 1` and the last increment takes `c` to `n <= u32::MAX`. Neither
// `c += 1` nor `i += 1` can overflow, for ANY `n`. The program is safe.
//
// So a refinement that makes this PASS has not over-fired; it has become
// complete on one more shape. The guard rail against over-firing is
// `loop_accumulator_correct_refusal_bounded_addend_really_overflows.rs`, which
// is genuinely unsafe. This file's expectation is `fail` because that is what
// the toolchain does today, not because failing is right.
pub fn f(n: u32) -> u32 {
    let mut c = 0u32;
    let mut i = 0u32;
    while i < n {
        c += 1;
        i += 1;
    }
    c
}
