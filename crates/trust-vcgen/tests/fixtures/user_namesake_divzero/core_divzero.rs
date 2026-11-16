// Controls: core's own zero-divisor methods keep their rows.
pub fn c1(a: u32, b: u32) -> u32 { a.div_ceil(b) }
pub fn c2(n: usize, k: usize) -> usize { (0..n).step_by(k).count() }
pub fn c3(a: i64, b: i64) -> i64 { a.rem_euclid(b) }
pub fn c4(a: i32, b: i32) -> i32 { a.div_euclid(b) }
pub struct It(pub u32);
impl Iterator for It {
    type Item = u32;
    fn next(&mut self) -> Option<u32> { None }
}
pub fn s1(k: usize) -> usize { It(0).step_by(k).count() }
pub fn s2(v: &[u32], k: usize) -> usize { v.iter().step_by(k).count() }
pub fn g1(a: u32, b: u32) -> u32 { if b != 0 { a.div_ceil(b) } else { 0 } }
