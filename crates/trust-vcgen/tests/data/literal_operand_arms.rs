// SELF-GUARDED-LITERAL-OPERAND-1: the source of `literal_<fn>.json` (README,
// "Literal operand family"). Each dump is the compiler's own extracted
// verification input for the function `<fn>`.
#![allow(arithmetic_overflow)]

// `-i32::MIN` panics ("attempt to negate with overflow") on every run. Under the
// allow, rustc keeps the checked `Neg` of a LITERAL operand:
// `Eq(const MIN, const MIN); assert(!_, OverflowNeg); Neg(const MIN)`.
pub fn neg_min() -> i32 {
    -i32::MIN
}

// The narrow width: `operand_ty` types the literal `-128` as i64.
pub fn neg_min8() -> i8 {
    -i8::MIN
}

// The safe twin: `-i32::MAX` cannot overflow, and keeps one honest row.
pub fn neg_max() -> i32 {
    -i32::MAX
}

// i128: both lanes take the bitvector constructors, so the suppression stays out.
pub fn neg_min128() -> i128 {
    -i128::MIN
}

// A LITERAL dividend over a computed divisor with ONE definition (`_2 = _1 as
// i16`), so a forged arm can move that definition into the overflow-assert block
// without making the divisor unstable function-wide.
pub fn div_cast_divisor(b: bool) -> i16 {
    7i16 / (b as i16)
}
