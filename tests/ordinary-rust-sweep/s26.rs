pub struct Acc {
    pub t: u64,
}
impl Acc {
    pub fn add(&mut self, v: u32) {
        self.t = self.t.wrapping_add(v as u64);
    }
}
