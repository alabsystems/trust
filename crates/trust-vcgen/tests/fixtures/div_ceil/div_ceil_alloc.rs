pub const MAX: usize = 1 << 16;
// Bounded: `n <= MAX` bounds `n.div_ceil(8)` by `MAX / 8`.
pub fn div_ceil_bounded(n: usize) -> Option<Vec<u8>> {
    if n > MAX {
        return None;
    }
    Some(vec![0u8; n.div_ceil(8)])
}
// Unbounded: no guard; `n.div_ceil(8)` reaches `usize::MAX / 8 + 1`.
pub fn div_ceil_unbounded(n: usize) -> Vec<u8> {
    vec![0u8; n.div_ceil(8)]
}
// Bounded numerator, divisor 1: `n.div_ceil(1) == n`, so the guard must be
// tight (the ceiling is exact, not an over-approximation that slips under).
pub fn div_ceil_by_one_over(n: usize) -> Option<Vec<u8>> {
    if n > (1usize << 40) {
        return None;
    }
    Some(vec![0u8; n.div_ceil(1)])
}
// u32 width.
pub fn div_ceil_u32(n: u32) -> Option<Vec<u8>> {
    if n > 4096 {
        return None;
    }
    Some(vec![0u8; n.div_ceil(3) as usize])
}
// Divisor zero: must still charge division by zero.
pub fn div_ceil_var_divisor(n: u64, d: u64) -> u64 {
    n.div_ceil(d)
}
// Tight bound, exact ceiling: n <= 8 * (2^28 - 1) gives a count <= 2^28 - 1,
// just under the 2^28 ceiling, so this PROVES.
pub fn div_ceil_tight_ok(n: usize) -> Option<Vec<u8>> {
    if n > 8 * ((1usize << 28) - 1) {
        return None;
    }
    Some(vec![0u8; n.div_ceil(8)])
}
// One more element: n = 8 * (2^28 - 1) + 1 rounds UP to exactly 2^28, so this
// must FAIL. A floor model (n / 8) would still give 2^28 - 1 and prove it.
pub fn div_ceil_tight_over(n: usize) -> Option<Vec<u8>> {
    if n > 8 * ((1usize << 28) - 1) + 1 {
        return None;
    }
    Some(vec![0u8; n.div_ceil(8)])
}
// Return slot: the ceiling of a u8 over 8 is at most 32 ...
pub fn div_ceil_ret_ok(n: u8) -> u8
    ensures result <= 32
{
    n.div_ceil(8)
}
// ... and reaches 32 (255 / 8 rounds up), so `<= 31` is false.
pub fn div_ceil_ret_over(n: u8) -> u8
    ensures result <= 31
{
    n.div_ceil(8)
}
