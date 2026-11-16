// User functions merely NAMED like core's zero-divisor methods (`div_ceil`,
// `rem_euclid`, `div_euclid`, `Iterator::step_by`); none divides, none can panic.
pub struct Q;
impl Q {
    #[inline(never)]
    pub fn div_ceil(a: u32, b: u32) -> u32 { a ^ b }
}
#[inline(never)]
pub fn rem_euclid(a: u32, b: u32) -> u32 { a | b }
#[inline(never)]
pub fn div_euclid(a: u64, b: u64) -> u64 { a & b }
pub struct S;
impl S {
    #[inline(never)]
    pub fn step_by(&self, n: usize) -> usize { n }
}
pub trait Euclid { fn rem_euclid(&self, v: &Self) -> Self; }
impl Euclid for u8 {
    #[inline(never)]
    fn rem_euclid(&self, v: &Self) -> Self { *self ^ *v }
}
pub fn p1(a: u32, b: u32) -> u32 { Q::div_ceil(a, b) }
pub fn p2(a: u32, b: u32) -> u32 { rem_euclid(a, b) }
pub fn p3(a: u64, b: u64) -> u64 { div_euclid(a, b) }
pub fn p4(s: &S) -> usize { s.step_by(0) }
pub fn p5(x: u8, y: u8) -> u8 { Euclid::rem_euclid(&x, &y) }
