#![crate_type = "lib"]
// PROVED (Imp5, slice-length <= isize::MAX): `s.len() + s.len()` cannot overflow `usize`. A
// slice length is `<= isize::MAX = 2^63 - 1` (no allocation exceeds isize::MAX bytes), so the
// sum is `<= 2^64 - 2 < usize::MAX`. The loose `usize` type range alone admits overflow, so
// before Imp5 this was ay-FAILED. The native `native_slice_len_value_facts` now emits
// `0 <= len <= isize::MAX` for every `Rvalue::Len`, discharging the add. Mirrors astream's
// `Frame` `HEADER_SIZE + payload.len()` length arithmetic. MUST verify (exit 0).
pub fn add_two_lens(s: &[u8]) -> usize {
    s.len() + s.len()
}
