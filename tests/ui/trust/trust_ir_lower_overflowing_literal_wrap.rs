//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
// The ConstTypeMismatch-cluster root-fix (full-population frontier,
// wave-full-0831): integer literals WRAP into their declared width. The old
// literal lowering assumed "typeck already rejected every out-of-range
// literal" — false under #[allow(overflowing_literals)]:
// `-9223372036854775808i32` type-checks, rustc TRUNCATES the literal into
// the type's width first (2^63 as i32 = 0) and then negates, while the
// producer negated at 128-bit width and minted `const i32 -2^63` — an
// unfitting constant (the validator's ConstTypeMismatch, measured on
// const-negation.rs and i128.rs) that was also SEMANTICALLY WRONG. Both
// literal paths now mask into the declared width — a no-op for every
// in-range literal (`i128::MIN` included), rustc's truncate-then-negate on
// the overflowing ones.
#![allow(overflowing_literals)]

pub fn wrapped_neg() -> u64 {
    // rustc: literal truncates to i32 (= 0), negation gives 0, cast gives 0.
    -9223372036854775808i32 as u64
}

pub fn wrapped_pos() -> u32 {
    // 2^40 truncates into u32's width.
    1099511627776i64 as u32 as u32
}

pub fn min_i128() -> i128 {
    // The one representable boundary the old path existed for — unchanged.
    -170141183460469231731687303715884105728i128
}
