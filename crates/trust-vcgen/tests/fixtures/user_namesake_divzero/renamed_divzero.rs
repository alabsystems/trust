// The twin of `user_divzero.rs`: byte-identical bodies, renamed off core's
// zero-divisor method names. The stage 1 of `46e9afaf95` accepts it.
pub struct Q;
impl Q {
    #[inline(never)]
    pub fn dceil(a: u32, b: u32) -> u32 { a ^ b }
}
#[inline(never)]
pub fn reuc(a: u32, b: u32) -> u32 { a | b }
#[inline(never)]
pub fn deuc(a: u64, b: u64) -> u64 { a & b }
pub struct S;
impl S {
    #[inline(never)]
    pub fn stepb(&self, n: usize) -> usize { n }
}
pub trait Euclid { fn reuc2(&self, v: &Self) -> Self; }
impl Euclid for u8 {
    #[inline(never)]
    fn reuc2(&self, v: &Self) -> Self { *self ^ *v }
}
pub fn p1(a: u32, b: u32) -> u32 { Q::dceil(a, b) }
pub fn p2(a: u32, b: u32) -> u32 { reuc(a, b) }
pub fn p3(a: u64, b: u64) -> u64 { deuc(a, b) }
pub fn p4(s: &S) -> usize { s.stepb(0) }
pub fn p5(x: u8, y: u8) -> u8 { Euclid::reuc2(&x, &y) }
