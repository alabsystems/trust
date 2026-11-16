// Adversarial probes for the integer-parameter type-range facts
// (trust_mir_extract::integer_param_range_preconditions) and every other place a
// type range is assumed. Naming:
//   bug_*  : a reachable panic (or a FALSE ensures). Any Proved row on its
//            assertion / postcondition is a FALSE PROOF.
//   ok_*   : a TRUE property. A refutation whose witness gives a typed integer
//            parameter an out-of-type value is the y=-1 FALSE-REFUTATION class.
// Witness in a comment on each bug_*.
#![allow(unused_assignments, unused_variables, clippy::all)]

use core::mem::transmute;

// ---------------------------------------------------------------- A: reinterpret a param
pub fn bug_a1_cast_i32_to_u32(x: i32) { let u = x as u32; assert!(u <= 0x7FFF_FFFF); } // x=-1
pub fn bug_a2_cast_u32_to_i32(x: u32) { let s = x as i32; assert!(s >= 0); } // x=2^31
pub fn bug_a3_cast_i64_to_u32(x: i64) { let u = x as u32; assert!(u as i64 == x); } // x=-1
pub fn bug_a4_cast_u64_to_i64(x: u64) { let s = x as i64; assert!(s >= 0); } // x=2^63
pub fn bug_a5_cast_i8_to_u8(x: i8) { let u = x as u8; assert!(u < 128); } // x=-1
pub fn bug_a6_cast_u8_to_i8(x: u8) { let s = x as i8; assert!(s >= 0); } // x=200
pub fn bug_a7_cast_i16_to_u64(x: i16) { let u = x as u64; assert!(u < 65536); } // x=-1
pub fn bug_a8_cast_usize_to_isize(x: usize) { let s = x as isize; assert!(s >= 0); } // x=2^63
pub fn bug_a9_cast_i32_to_usize(x: i32) { let u = x as usize; assert!(u < (1usize << 31)); } // x=-1
pub fn bug_a10_transmute_u32_i32(x: u32) { let s: i32 = unsafe { transmute(x) }; assert!(s >= 0); } // x=2^31
pub fn bug_a11_transmute_i64_u64(x: i64) { let u: u64 = unsafe { transmute(x) }; assert!(u <= i64::MAX as u64); } // x=-1
union U32I32 { a: u32, b: i32 }
pub fn bug_a12_union_u32_i32(x: u32) { let v = U32I32 { a: x }; let b = unsafe { v.b }; assert!(b >= 0); } // x=2^31
union I8U8 { a: i8, b: u8 }
pub fn bug_a13_union_i8_u8(x: i8) { let v = I8U8 { a: x }; let b = unsafe { v.b }; assert!(b < 128); } // x=-1
pub fn bug_a14_rawptr_u32_i32(x: u32) { let p = &x as *const u32 as *const i32; let b = unsafe { *p }; assert!(b >= 0); } // x=2^31
pub fn bug_a15_rawptr_i16_u16(x: i16) { let p = &x as *const i16 as *const u16; let b = unsafe { *p }; assert!(b < 0x8000); } // x=-1
pub fn bug_a16_cast_signed(x: u32) { let s = x.cast_signed(); assert!(s >= 0); } // x=2^31
pub fn bug_a17_cast_unsigned(x: i64) { let u = x.cast_unsigned(); assert!(u <= i64::MAX as u64); } // x=-1
pub fn bug_a18_from_ne_bytes(x: u32) { let s = i32::from_ne_bytes(x.to_ne_bytes()); assert!(s >= 0); } // x=2^31
pub fn bug_a19_char_as_u8(c: char) { let b = c as u8; assert!(b as u32 == c as u32); } // c='\u{100}'
pub fn bug_a20_i64_as_i8_roundtrip(x: i64) { let t = x as i8; assert!(t as i64 == x); } // x=128
pub fn bug_a21_u16_as_i16_as_i32(x: u16) { let s = x as i16 as i32; assert!(s >= 0); } // x=0x8000
pub fn bug_a22_double_transmute(x: i8) { let u: u8 = unsafe { transmute(x) }; let w = u as u32; assert!(w < 128); } // x=-1

// ---------------------------------------------------------------- B: wrapping results
pub fn bug_b1_wrapping_add(x: u32) { let y = x.wrapping_add(1); assert!(y > x); } // x=MAX
pub fn bug_b2_wrapping_sub(x: u8) { let y = x.wrapping_sub(1); assert!(y < x); } // x=0
pub fn bug_b3_wrapping_neg(x: i32) { let y = x.wrapping_neg(); assert!(x == 0 || y != x); } // x=MIN
pub fn bug_b4_wrapping_mul(x: u16) { let y = x.wrapping_mul(2); assert!(y >= x); } // x=40000
pub fn bug_b5_wrapping_shl(x: u32) { let y = x.wrapping_shl(1); assert!(y >= x); } // x=2^31
pub fn bug_b6_overflowing_add(x: i64) { let (y, _) = x.overflowing_add(1); assert!(y > x); } // x=MAX
pub fn bug_b7_wrapping_abs(x: i8) { let y = x.wrapping_abs(); assert!(y >= 0); } // x=-128
pub fn bug_b8_wrapping_newtype(x: u32) { let y = core::num::Wrapping(x) + core::num::Wrapping(1); assert!(y.0 > x); } // x=MAX
pub fn bug_b9_wrapping_add_signed(x: i16) { let y = x.wrapping_add(1); assert!(y > x); } // x=MAX
pub fn bug_b10_wrapping_sub_usize(x: usize) { let y = x.wrapping_sub(1); assert!(y < x); } // x=0
pub fn bug_b11_wrapping_mul_i32(x: i32) { let y = x.wrapping_mul(-1); assert!(x == 0 || y != x); } // x=MIN
pub fn bug_b12_wrapping_add_then_cmp(x: u64, y: u64) { let s = x.wrapping_add(y); assert!(s >= x); } // x=MAX,y=1

// ---------------------------------------------------------------- C: `mut` params reassigned
pub fn bug_c1_mut_cast(mut x: u32, y: i64) -> u32 { x = y as u32; assert!(y >= 0 && y <= 4294967295); x } // y=-1
pub fn bug_c2_mut_cast_i8(mut x: i8, y: u8) -> i8 { x = y as i8; assert!(y < 128); x } // y=200
pub fn bug_c3_mut_transmute(mut x: u32, y: i32) -> u32 { x = unsafe { transmute(y) }; assert!(y >= 0); x } // y=-1
pub fn bug_c4_mut_wrapping(mut x: u32, y: u32) -> u32 { x = y.wrapping_add(1); assert!(y != u32::MAX); x } // y=MAX
pub fn bug_c5_mut_truncate(mut x: u8, y: u32) -> u8 { x = y as u8; assert!(y < 256); x } // y=256
pub fn bug_c6_mut_through_ref(mut x: u32, y: i64) -> u32 { let r = &mut x; *r = y as u32; assert!(y >= 0); x } // y=-1
pub fn bug_c7_mut_through_raw(mut x: u32, y: i32) -> u32 { let p = &mut x as *mut u32 as *mut i32; unsafe { *p = y }; assert!(x as i64 == y as i64); x } // y=-1
pub fn bug_c8_mut_self_wrap(mut x: u32) -> u32 { let orig = x; x = x.wrapping_add(1); assert!(x > orig); x } // x=MAX
pub fn bug_c9_mut_union(mut x: u32, y: i32) -> u32 { let v = U32I32 { b: y }; x = unsafe { v.a }; assert!(y >= 0); x } // y=-1
pub fn bug_c10_mut_loop_wrap(mut x: u8, n: u8) -> u8 { let start = x; for _ in 0..n { x = x.wrapping_add(1); } assert!(x >= start); x } // x=255,n=1
pub fn bug_c11_mut_reassign_signed(mut x: i32, y: u32) -> i32 { x = y as i32; assert!(y <= i32::MAX as u32); x } // y=2^31
pub fn bug_c12_mut_param_swap(mut x: u16, mut y: i16) -> u16 { x = y as u16; y = 5; assert!(x < 0x8000); x } // y=-1

// ---------------------------------------------------------------- D: enum discriminants
#[repr(i8)] #[derive(Clone, Copy)] pub enum Ei8 { A = -1, B = 1 }
pub fn bug_d1_neg_disc_as_u8(e: Ei8) { let d = e as u8; assert!(d < 128); } // A
#[repr(u8)] #[derive(Clone, Copy)] pub enum Eu8 { A = 255, B = 0 }
pub fn bug_d2_high_disc_as_i8(e: Eu8) { let d = e as i8; assert!(d >= 0); } // A
#[repr(i32)] #[derive(Clone, Copy)] pub enum Ei32 { A = -5, B = 7 }
pub fn bug_d3_neg_disc_as_u32(e: Ei32) { let d = e as u32; assert!(d < 100); } // A
#[repr(i64)] #[derive(Clone, Copy)] pub enum Ei64 { A = i64::MIN, B = 0 }
pub fn bug_d4_min_disc_as_u64(e: Ei64) { let d = e as u64; assert!(d < (1u64 << 63)); } // A
pub fn bug_d5_neg_disc_as_usize(e: Ei8) { let d = e as usize; assert!(d < 256); } // A
pub fn bug_d6_disc_into_mut_param(mut x: u8, e: Ei8) -> u8 { x = e as u8; assert!(matches!(e, Ei8::B)); x } // A
#[repr(u16)] #[derive(Clone, Copy)] pub enum Eu16 { A = 0xFFFF, B = 1 }
pub fn bug_d7_disc_as_i16_into_i32(e: Eu16) { let d = e as i16 as i32; assert!(d > 0); } // A

// ---------------------------------------------------------------- E: postconditions (native contracts)
pub fn bug_e1_post_cast_signed(x: u32) -> i32 ensures result >= 0 { x as i32 } // x=2^31
pub fn bug_e2_post_cast_unsigned(x: i32) -> u32 ensures result <= 2147483647 { x as u32 } // x=-1
pub fn bug_e3_post_wrapping(x: u32) -> u32 ensures result > x { x.wrapping_add(1) } // x=MAX
pub fn bug_e4_post_truncate(x: u64) -> u8 ensures result == x { x as u8 } // x=256
pub fn bug_e5_post_transmute(x: u32) -> i32 ensures result >= 0 { unsafe { transmute(x) } } // x=2^31
pub fn bug_e6_post_mut_param(mut x: u32, y: i64) -> i64 ensures result >= 0 { x = y as u32; y } // y=-1
pub fn bug_e7_post_union(x: u32) -> i32 ensures result >= 0 { let v = U32I32 { a: x }; unsafe { v.b } } // x=2^31
pub fn bug_e8_post_wrapping_neg(x: i32) -> i32 ensures result >= 0 || x > 0 { x.wrapping_neg() } // x=MIN
pub fn bug_e9_post_disc(e: Ei8) -> u8 ensures result < 128 { e as u8 } // A
pub fn bug_e10_post_char_u8(c: char) -> u8 ensures result as u32 == c as u32 { c as u8 } // c=256

// ---------------------------------------------------------------- F: TRUE properties (y=-1 class, every width)
pub fn ok_f1_u8_sat_add(x: u8, y: u8) -> u8 ensures result >= x { x.saturating_add(y) }
pub fn ok_f2_u16_sat_add(x: u16, y: u16) -> u16 ensures result >= x { x.saturating_add(y) }
pub fn ok_f3_u32_sat_add(x: u32, y: u32) -> u32 ensures result >= x { x.saturating_add(y) }
pub fn ok_f4_u64_sat_add(x: u64, y: u64) -> u64 ensures result >= x { x.saturating_add(y) }
pub fn ok_f5_usize_sat_add(x: usize, y: usize) -> usize ensures result >= x { x.saturating_add(y) }
pub fn ok_f6_u8_sat_sub(x: u8, y: u8) -> u8 ensures result <= x { x.saturating_sub(y) }
pub fn ok_f7_u64_sat_sub(x: u64, y: u64) -> u64 ensures result <= x { x.saturating_sub(y) }
pub fn ok_f8_i8_widen_lo(x: i8) -> i16 ensures result >= -128 { x as i16 }
pub fn ok_f9_i8_widen_hi(x: i8) -> i16 ensures result <= 127 { x as i16 }
pub fn ok_f10_i16_widen(x: i16) -> i32 ensures result >= -32768 && result <= 32767 { x as i32 }
pub fn ok_f11_i32_widen(x: i32) -> i64 ensures result >= -2147483648 && result <= 2147483647 { x as i64 }
pub fn ok_f12_i64_widen(x: i64) -> i128 ensures result >= -9223372036854775808 && result <= 9223372036854775807 { x as i128 }
pub fn ok_f13_isize_widen(x: isize) -> i128 ensures result >= -9223372036854775808 { x as i128 }
pub fn ok_f14_u8_widen(x: u8) -> u32 ensures result <= 255 { x as u32 }
pub fn ok_f15_u16_widen(x: u16) -> u64 ensures result <= 65535 { x as u64 }
pub fn ok_f16_u32_widen(x: u32) -> u64 ensures result <= 4294967295 { x as u64 }
pub fn ok_f17_u64_widen(x: u64) -> u128 ensures result <= 18446744073709551615 { x as u128 }
pub fn ok_f18_usize_widen(x: usize) -> u128 ensures result <= 18446744073709551615 { x as u128 }
pub fn ok_f19_i16_sat_add_nonneg(x: i16, y: i16) -> i16 requires y >= 0 ensures result >= x { x.saturating_add(y) }
pub fn ok_f20_i64_sat_sub_nonneg(x: i64, y: i64) -> i64 requires y >= 0 ensures result <= x { x.saturating_sub(y) }
pub fn ok_f21_u128_identity(x: u128) -> u128 ensures result >= 0 { x }
pub fn ok_f22_i128_widen_hi(x: i128) -> i128 ensures result <= 170141183460469231731687303715884105727 { x }
pub fn ok_f23_u32_unsigned_abs(x: i32) -> u32 ensures result <= 2147483648 { x.unsigned_abs() }
pub fn ok_f24_u8_mut_param(mut x: u8, y: u8) -> u8 ensures result >= y { x = x.saturating_add(0); x.max(y) }
pub fn ok_f25_u16_assert(x: u16) { assert!(x as u32 <= 65535); }
pub fn ok_f26_i8_assert(x: i8) { assert!(x as i32 >= -128); }
pub fn ok_f27_u64_assert(x: u64) { assert!(x as u128 <= u64::MAX as u128); }
pub fn ok_f28_i32_assert(x: i32) { assert!((x as i64) <= i32::MAX as i64); }
pub fn ok_f29_char_assert(c: char) { assert!((c as u32) <= 0x10FFFF); }
pub fn ok_f30_u32_index(x: u32) -> u32 { let a = [0u32; 4]; if x < 4 { a[x as usize] } else { 0 } }
pub fn ok_f31_i32_div(x: i32) -> i32 { if x > 0 { 100 / x } else { 0 } }
pub fn ok_f32_u8_sub_guard(x: u8) -> u8 { if x >= 1 { x - 1 } else { 0 } }

// ---------------------------------------------------------------- G: bit ops / div / rem on params
pub fn bug_g1_not_u8(x: u8) { let y = !x; assert!(y < 255); } // x=0
pub fn bug_g2_not_u32(x: u32) { let y = !x; assert!(y != 0); } // x=MAX
pub fn bug_g3_not_i8(x: i8) { let y = !x; assert!(y < 127); } // x=-128
pub fn bug_g4_xor_u16(x: u16) { let y = x ^ 0xFFFF; assert!(y <= x); } // x=0
pub fn bug_g5_and_i32(x: i32) { let y = x & -2; assert!(y >= 0); } // x=-1
pub fn bug_g6_or_u8(x: u8) { let y = x | 0x80; assert!(y < 0x80 || x >= 0x80); } // x=0
pub fn bug_g7_shr_i32(x: i32) { if x < 0 { let y = x >> 1; assert!(y > x / 2 - 1 && y != x); } } // x=-1 (-1>>1 == -1 == x)
pub fn bug_g8_div_trunc(x: i32) { if x < 0 { let q = x / 2; assert!(q < 0); } } // x=-1 (q=0)
pub fn bug_g9_rem_sign(x: i32) { if x < 0 && x % 2 != 0 { assert!(x % 2 == 1); } } // x=-1 (rem=-1)
pub fn bug_g10_rotate(x: u32) { let y = x.rotate_left(1); assert!(y >= x || x >= 0x8000_0000); } // never panics? control: rotl(x)=2x for x<2^31 -> true; see g11
pub fn bug_g11_rotate_hi(x: u32) { let y = x.rotate_left(1); assert!(y >= x); } // x=2^31 (y=1)
pub fn bug_g12_swap_bytes(x: u32) { let y = x.swap_bytes(); assert!(y <= x || x < 0x100); } // x=0x100 (y=0x10000)
pub fn bug_g13_shl_u8(x: u8) { let y = x << 1; assert!(y >= x); } // x=200 (O0: overflow check on shift amount only)
pub fn bug_g14_neg_cast_mix(x: u8) { let y = (x as i8).wrapping_neg() as u8; assert!(y <= x || x == 0 || x > 128); } // x=129? (-(−127)=127 ≤129 ok) ... x=128: (-128).wrapping_neg()=-128 -> 128 <= 128 ok; x=1: 255 > 1 -> panic
pub fn bug_g15_rem_euclid(x: i32) { let r = x.rem_euclid(3); assert!(r == x % 3); } // x=-1
pub fn bug_g16_div_euclid(x: i32) { let q = x.div_euclid(2); assert!(q == x / 2); } // x=-1

// ---------------------------------------------------------------- M: uninit / padding (UB)
pub fn bug_m1_assume_init_uninit(x: u32) -> u32 { let m = core::mem::MaybeUninit::<u32>::uninit(); unsafe { m.assume_init() } } // UB
#[repr(C)] #[derive(Clone, Copy)] pub struct Pad { a: u8, b: u32 }
pub fn bug_m2_padding_transmute(a: u8, b: u32) -> u64 { let p = Pad { a, b }; unsafe { transmute::<Pad, u64>(p) } } // UB (padding)

// ---------------------------------------------------------------- H: the y=-1 class at 128 bits (outside the extractor's <=64 envelope)
pub fn ok_h1_u128_sat_add(x: u128, y: u128) -> u128 ensures result >= x { x.saturating_add(y) }
pub fn ok_h2_u128_sat_sub(x: u128, y: u128) -> u128 ensures result <= x { x.saturating_sub(y) }
pub fn ok_h3_i128_sat_add_nonneg(x: i128, y: i128) -> i128 requires y >= 0 ensures result >= x { x.saturating_add(y) }
pub fn ok_h4_u128_assert(x: u128, y: u128) { let s = x.saturating_add(y); assert!(s >= x); }
pub fn ok_h5_u128_widen_ret(x: u64) -> u128 ensures result <= 18446744073709551615 { x as u128 }
pub fn ok_h6_i128_param_hi(x: i128) -> bool ensures result == true { x <= i128::MAX }
pub fn ok_h7_u128_param_lo(x: u128) -> bool ensures result == true { x >= 0 }
pub fn ok_h8_u32_sat_add_assert(x: u32, y: u32) { let s = x.saturating_add(y); assert!(s >= x); }
pub fn ok_h9_i8_sat_sub_assert(x: i8, y: i8) { if y >= 0 { let s = x.saturating_sub(y); assert!(s <= x); } }
pub fn ok_h10_isize_sat_add_assert(x: isize, y: isize) { if y >= 0 { let s = x.saturating_add(y); assert!(s >= x); } }

// ---------------------------------------------------------------- I: discriminant temp / named locals mutated after the fact
#[repr(u8)] #[derive(Clone, Copy)] pub enum Eu8b { A = 1, B = 2 }
pub fn bug_i1_disc_local_mut(e: Eu8b) { let mut d = e as u8; let r = &mut d; *r = 3; assert!(d != 3); } // always panics
pub fn bug_i2_disc_local_raw(e: Eu8b) { let mut d = e as u8; let p = &mut d as *mut u8; unsafe { *p = 3 }; assert!(d != 3); } // always panics
pub fn bug_i3_disc_local_loop(e: Eu8b, n: u8) { let mut d = e as u8; for _ in 0..n { d = d.wrapping_add(1); } assert!(d <= 2); } // n=2
pub fn bug_i4_param_mut_ref_write(mut x: u8, y: u8) { let r = &mut x; *r = y; assert!(x == y); assert!(y < 200); } // y=200
