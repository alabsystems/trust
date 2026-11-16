// Compiled with -C overflow-checks=off: `+ - *` are plain (WRAPPING) MIR BinaryOps.
// bug_*: reachable panic / false ensures under wrapping semantics.
#![allow(unused_assignments, clippy::all)]
pub fn bug_r1_mut_param_add(mut x: u32) -> u32 { x = x + 1; assert!(x > 0); x } // x=MAX
pub fn bug_r2_local_add(x: u32) { let y = x + 1; assert!(y > x); } // x=MAX
pub fn bug_r3_two_param_add(x: u8, y: u8) { let s = x + y; assert!(s >= x); } // 200,100
pub fn bug_r4_post_add(x: u32) -> u32 ensures result > x { x + 1 } // x=MAX
pub fn bug_r5_mut_param_mul(mut x: u16) -> u16 { x = x * 2; assert!(x >= 2 || x == 0); x } // x=32768 -> 0? (0 passes) ; x=32769 -> 2 passes; use r6
pub fn bug_r6_mul_cmp(x: u16) { let y = x * 2; assert!(y >= x); } // x=40000
pub fn bug_r7_sub_signed(x: i8) { let y = x - 1; assert!(y < x); } // x=-128
pub fn bug_r8_mut_param_sub(mut x: usize) -> usize { x = x - 1; assert!(x < usize::MAX); x } // x=0
pub fn bug_r9_neg(x: i32) { let y = -x; assert!(x == 0 || y != x); } // x=MIN
pub fn bug_r10_post_mut_param(mut x: u8) -> u8 ensures result >= 1 { x = x + 1; x } // x=255
pub fn bug_r11_loop(mut x: u8, n: u8) -> u8 { let s = x; let mut i = 0; while i < n { x = x + 1; i = i + 1; } assert!(x >= s); x } // x=255,n=1
pub fn bug_r12_shl(x: u32) { let y = x << 1; assert!(y >= x); } // x=2^31
pub fn ok_r13_add_guarded(x: u32) { if x < 100 { let y = x + 1; assert!(y > x); } }
