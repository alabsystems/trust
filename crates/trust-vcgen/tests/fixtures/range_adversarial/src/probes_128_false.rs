// FALSE properties over 128-bit parameters and over call-defined returns: each must
// stay unproved once the generator states the 128-bit parameter ranges and the
// call-return tripwire is in place. The witness is in the trailing comment.
pub fn bug_w1_u128_identity_ge1(x: u128) -> u128 ensures result >= 1 { x } // x=0
pub fn bug_w2_i128_identity_nonneg(x: i128) -> i128 ensures result >= 0 { x } // x=-1
pub fn bug_w3_u128_below_max(x: u128) -> bool ensures result == true { x < u128::MAX } // x=u128::MAX
pub fn bug_w4_i128_above_min(x: i128) -> bool ensures result == true { x > i128::MIN } // x=i128::MIN
pub fn bug_w5_u128_as_i128_nonneg(x: u128) -> i128 ensures result >= 0 { x as i128 } // x=2^127
pub fn bug_w6_i128_as_u128_half(x: i128) -> u128 ensures result <= 170141183460469231731687303715884105727 { x as u128 } // x=-1
pub fn bug_w7_u128_mut_wrapping_add(mut x: u128) -> u128 ensures result >= 1 { x = x.wrapping_add(1); x } // x=u128::MAX
pub fn bug_w8_u128_wrapping_sub(x: u128) -> u128 ensures result < x { x.wrapping_sub(1) } // x=0
pub fn bug_w9_u128_assert_below_max(x: u128) { assert!(x < u128::MAX); } // x=u128::MAX
pub fn bug_w10_i128_assert_not_min(x: i128) { assert!(x != i128::MIN); } // x=i128::MIN
pub fn bug_w11_u128_within_u64(x: u128) -> u128 ensures result <= 18446744073709551615 { x } // x=2^64
pub fn bug_w12_u128_mut_through_ref(mut x: u128) -> u128 ensures result >= 1 { let r = &mut x; *r = 0; x } // any x
pub fn bug_w13_i128_wrapping_neg(x: i128) -> i128 ensures result >= 0 { x.wrapping_neg() } // x=i128::MIN
pub fn bug_w14_i128_within_i64(x: i128) -> i128 ensures result >= -9223372036854775808 { x } // x=i128::MIN
// A MODELED call keeps a real refutation (the tripwire must not swallow it).
pub fn bug_w15_u32_sat_add_gt(x: u32, y: u32) -> u32 ensures result > x { x.saturating_add(y) } // y=0
pub fn bug_w16_u64_sat_sub_lt(x: u64, y: u64) -> u64 ensures result < x { x.saturating_sub(y) } // y=0
// The COST of the call-return tripwire: a FALSE clause over an UNMODELED sysroot call is
// no longer refuted (its `_0` is free, so no witness is an execution); it is unverifiable.
pub fn bug_w17_i32_unsigned_abs_lt5(x: i32) -> u32 ensures result < 5 { x.unsigned_abs() } // x=5
pub fn bug_w18_u128_sat_add_gt(x: u128, y: u128) -> u128 ensures result > x { x.saturating_add(y) } // y=0
