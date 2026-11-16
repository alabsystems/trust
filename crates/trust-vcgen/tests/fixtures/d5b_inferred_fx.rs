pub fn guard(bit: u32) -> bool { bit < 64 }
pub fn shift_via_guard(x: u64, bit: u32) -> Option<u64> {
    if !guard(bit) { return None; }
    Some(x >> bit)
}
pub fn nz(d: u32) -> u32 { if d == 0 { 1 } else { d } }
pub fn div_nz(x: u32, d: u32) -> u32 { x / nz(d) }
pub fn cell_width_ok(cell: u32) -> bool { cell > 0 }
pub fn cell_index(rel: u32, cell: u32) -> Option<u32> {
    if !cell_width_ok(cell) { return None; }
    Some(rel / cell)
}
pub fn guard_bad(bit: u32) -> bool { bit < 65 }
pub fn shift_bad(x: u64, bit: u32) -> Option<u64> {
    if !guard_bad(bit) { return None; }
    Some(x >> bit)
}
pub fn g_or(b: u32) -> bool { b < 64 || b == 64 }
pub fn shift_or(x: u64, bit: u32) -> Option<u64> {
    if !g_or(bit) { return None; }
    Some(x >> bit)
}
pub fn g_not(b: u32) -> bool { let t = b < 64; !t }
pub fn shift_not(x: u64, bit: u32) -> Option<u64> {
    if !g_not(bit) { return None; }
    Some(x >> bit)
}
pub fn g_and(a: u32, b: u32) -> bool { a < 8 && b < 8 }
pub fn pick(c: bool, a: u32, b: u32) -> u32 { if c { a } else { b } }
pub fn sgn(x: i32) -> i32 { if x < 0 { -1 } else if x == 0 { 0 } else { 1 } }
pub fn m(x: u32) -> u32 { match x { 0 => 5, 1 => 7, _ => x } }
pub fn neg_m(x: i8) -> i8 { match x { -1 => 3, -128 => 4, _ => x } }
pub fn bxor(a: bool, b: bool) -> bool { a ^ b }
pub fn band(a: bool, b: bool) -> bool { a & b }
pub fn ext_guard(bit: u32) -> bool { bit.leading_zeros() > 25 }
pub fn scale(k: u32) -> u32 { k * 8 }
pub fn widen(x: u8) -> u32 { x as u32 }
pub fn loop_helper(n: u32) -> u32 { let mut i = 0; while i < n { i += 1; } i }
pub fn by_ref(r: &u32) -> bool { *r < 64 }
pub fn le(a: u32, b: u32) -> bool { a <= b }
pub fn sub_via_le(a: u32, b: u32) -> Option<u32> {
    if !le(a, b) { return None; }
    Some(b - a)
}
pub fn unguarded_after_guard(x: u64, bit: u32) -> u64 {
    let _ = guard(bit);
    x >> bit
}
pub mod ma { pub fn guard(bit: u32) -> bool { bit < 64 } }
pub mod mb { pub fn guard(bit: u32) -> bool { bit < 65 } }
pub fn shift_ma(x: u64, bit: u32) -> Option<u64> {
    if !ma::guard(bit) { return None; }
    Some(x >> bit)
}
pub fn shift_mb(x: u64, bit: u32) -> Option<u64> {
    if !mb::guard(bit) { return None; }
    Some(x >> bit)
}
