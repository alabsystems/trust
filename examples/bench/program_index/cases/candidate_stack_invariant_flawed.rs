// Candidate proof fixture: flawed stack capacity invariant.

struct TinyStack {
    data: [u32; 4],
    len: usize,
}

impl TinyStack {
    fn new() -> Self {
        Self { data: [0; 4], len: 0 }
    }

    fn push(&mut self, value: u32) -> bool {
        self.len += 1;
        self.data[self.len] = value;
        true
    }

    fn top(&self) -> Option<u32> {
        if self.len == 0 { None } else { Some(self.data[self.len - 1]) }
    }
}

fn main() {
    let mut stack = TinyStack::new();
    assert!(stack.push(5));
    let _ = stack.top();
}
