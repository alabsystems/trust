pub struct Out {
    n: usize,
}

impl Out {
    #[inline(never)]
    pub fn is_full(&self) -> bool {
        std::hint::black_box(self.n) >= 16
    }
}

pub fn bulk_3byte(bytes: &[u8], out: &Out) -> usize {
    let mut i = 0usize;
    while !out.is_full() {
        match bytes.get(i..i + 3) {
            Some(_) => i += 3,
            None => break,
        }
    }
    i
}

pub fn pre(x: u8, n: u32) -> u8 {
    let y = x + 1;
    let mut i = 0;
    while i < n {
        i += 1;
    }
    y
}
