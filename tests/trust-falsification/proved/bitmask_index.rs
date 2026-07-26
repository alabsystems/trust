#![crate_type = "lib"]
// A power-of-two bitmask index into a fixed-size array, `s[i & 15]` on `[i32; 16]`
// (the ring-buffer / hash-table idiom). rustc keeps a runtime bounds check; Trust
// discharges it STATICALLY. vcgen conjoins the unconditional bitmask result bound
// `i & 15 <= 15` (a bitwise AND with mask `m` can only clear bits, so the result
// is `<= m` for any unsigned operand). With `15 < 16`, the violation `i&15 >= 16`
// contradicts `i&15 <= 15`; the clean CIC kernel certifies it via the
// single-variable interval over the masked-result variable (the bitvector
// `Eq(_3, BvAnd(..))` definition is soundly dropped). -full kernel-Certified.
pub fn bitmask_index(s: &[i32; 16], i: usize) -> i32 {
    s[i & 15]
}
