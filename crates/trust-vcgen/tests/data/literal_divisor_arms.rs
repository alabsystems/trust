// SELF-GUARDED-LITERAL-OPERAND-1, literal-divisor follow-up: the source of
// `literal_divisor_<fn>.json` (README, "Literal divisor family"). Each dump is the
// compiler's own extracted verification input for the function `<fn>`.
//
// Under `#![allow(unconditional_panic)]` rustc keeps the zero check of a LITERAL
// divisor: `Eq(const 0, const 0); assert(!_, DivisionByZero)`, and for a signed
// operation the intervening `Eq(const 0, const -1) & Eq(lhs, const MIN)` overflow
// assert. Each function below except `div_x5` panics on every call.
#![allow(arithmetic_overflow, unconditional_panic)]

// Signed: the zero check, then the overflow assert, then the division (the chain).
pub fn div_x0(x: i32) -> i32 {
    x / 0
}

pub fn rem_x0(x: i32) -> i32 {
    x % 0
}

// Unsigned: the zero check lands directly on the operation (one hop).
pub fn rem_u8_0(a: u8) -> u8 {
    a % 0u8
}

pub fn div_u32_0(a: u32) -> u32 {
    a / 0
}

// Both operands width-less signed literals: the chain reads INT_MIN at the
// destination's width.
pub fn div_lit_lit0() -> i32 {
    100 / 0
}

// A cast dividend (the scout corpus's `w6progs/1005/vlib.rs` shape).
pub fn rem_cast_0() -> u8 {
    (false as u8) % 0u8
}

// Control: a nonzero literal divisor has no statement-lane zero-divisor row at all
// (`v2_divisor_is_nonzero_constant`), and its assert-lane row is true.
pub fn div_x5(x: i32) -> i32 {
    x / 5
}
