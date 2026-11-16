pub fn bytes_count(s: &str) -> usize {
    s.bytes().filter(|b| *b == b'\n').count() + 1
}

pub fn bytes_count_underflow(s: &str) -> usize {
    s.bytes().filter(|b| *b == b'\n').count() - 1
}

pub fn split_count_not_bounded_by_bytes(s: &str) -> usize {
    s.len() - s.split("").count()
}

pub fn reassigned_root(s1: &str, s2: &str) -> usize {
    let mut s = s1;
    let it = s.bytes();
    s = s2;
    s.len() - it.count()
}

pub struct UserBytes;
impl Iterator for UserBytes {
    type Item = u8;
    fn next(&mut self) -> Option<u8> { None }
    fn count(self) -> usize { usize::MAX }
}
impl UserBytes {
    pub fn bytes(self) -> UserBytes { self }
}

pub fn custom_count_must_overflow() -> usize {
    UserBytes.bytes().count() + 1
}
