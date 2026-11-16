pub struct Counter {
    n: u32,
}
impl Counter {
    pub fn new() -> Self {
        Counter { n: 0 }
    }
    pub fn bump(&mut self) {
        self.n = self.n.saturating_add(1);
    }
    pub fn get(&self) -> u32 {
        self.n
    }
}
pub fn run(times: u32) -> u32 {
    let mut c = Counter::new();
    let mut i = 0u32;
    while i < times.min(100) {
        c.bump();
        i += 1;
    }
    c.get()
}
