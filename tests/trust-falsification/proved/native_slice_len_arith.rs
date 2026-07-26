#![crate_type = "lib"]
// Native CHC/PDR proof over a slice LENGTH: `s.len() + 1` cannot overflow because
// a slice's length is bounded by isize::MAX (so len + 1 <= isize::MAX + 1 <
// usize::MAX). The native typed trust-mc lane models the fat-pointer length
// metadata as a bounded symbolic [0, isize::MAX] and PROVES this under the
// default strict policy (it was previously Unsupported — the length was opaque).
pub fn native_slice_len_arith(s: &[u32]) -> usize {
    s.len() + 1
}
