#![no_std]
pub struct Endless {
    pub i: u64,
}
impl Iterator for Endless {
    type Item = u64;
    #[inline(never)]
    fn next(&mut self) -> Option<u64> {
        self.i = self.i.wrapping_add(1);
        Some(0)
    }
}
