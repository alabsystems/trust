#![crate_type = "lib"]
// Match on a TOTAL-CALL RESULT: `match s.first() { Some(&x) => x, None => 0 }`.
// `s.first()` is modeled as a fresh-symbolic `Undef` Option, DEFINED in the call
// block and field-extracted/matched in a successor block. The native CHC now
// threads that SSA-immutable value across the block boundary by dominance (like a
// function parameter), so its discriminant `ExtractField` resolves and the
// exhaustive match's otherwise→unreachable discharges. Combined with the
// `ValidBorrow` reference-payload load, the whole function is statically
// panic-free under the default strict policy.
pub fn match_call_result(s: &[i32]) -> i32 {
    match s.first() {
        Some(&x) => x,
        None => 0,
    }
}
