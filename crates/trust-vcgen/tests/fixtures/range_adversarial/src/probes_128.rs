// TRUE properties over 128-bit parameters (outside the extractor's width<=64 range-fact envelope).
pub fn ok_f21_u128_identity(x: u128) -> u128 ensures result >= 0 { x }
pub fn ok_f22_i128_identity_hi(x: i128) -> i128 ensures result <= 170141183460469231731687303715884105727 { x }
pub fn ok_h1_u128_sat_add(x: u128, y: u128) -> u128 ensures result >= x { x.saturating_add(y) }
pub fn ok_h2_u128_sat_sub(x: u128, y: u128) -> u128 ensures result <= x { x.saturating_sub(y) }
pub fn ok_h6_i128_param_hi(x: i128) -> bool ensures result == true { x <= i128::MAX }
pub fn ok_h7_u128_param_lo(x: u128) -> bool ensures result == true { x >= 0 }
pub fn ok_h7b_u128_cmp_zero(x: u128) -> bool ensures result == false { x < 0 }
pub fn ok_f23_u32_unsigned_abs(x: i32) -> u32 ensures result <= 2147483648 { x.unsigned_abs() }
pub fn ok_c1_u64_identity(x: u64) -> u64 ensures result >= 0 { x }
pub fn ok_c2_u32_sat_add(x: u32, y: u32) -> u32 ensures result >= x { x.saturating_add(y) }
