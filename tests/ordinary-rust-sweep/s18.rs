pub struct C {
    pub n: u32,
}
impl C {
    pub fn bump(&mut self) {
        self.n = self.n.saturating_add(1);
    }
}
