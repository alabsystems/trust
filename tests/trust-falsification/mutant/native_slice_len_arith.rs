#![crate_type = "lib"]
// MUTANT of proved/native_slice_len_arith.rs: `s.len() + k` with an UNBOUNDED
// `k`. The slice length bound (<= isize::MAX) does NOT bound the sum: for k near
// usize::MAX, `len + k` overflows. MUST be refused (exit 1) — proving the
// length-bound modeling is non-vacuous, not "prove every len-arithmetic".
pub fn native_slice_len_arith(s: &[u32], k: usize) -> usize {
    s.len() + k
}
