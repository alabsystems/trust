// DIRECTION 1 — a completeness gap that rustc still checks at runtime.
//
// `(a as u16) * (b as u16)` is a non-constant multiply: the interval domain
// cannot bound it, so its ArithmeticOverflow obligation does not discharge. That
// kind HAS a runtime fallback under `-C overflow-checks=on`, so policy B keeps
// rustc's check and the build SUCCEEDS. Under `certify` it must be rejected.
//
// Do not "simplify" this to a constant multiply: `(v as u16) * 2` PROVES since
// B.4, which would make this fixture measure nothing.
pub fn widen_mul(a: u8, b: u8) -> u16 {
    (a as u16) * (b as u16)
}
