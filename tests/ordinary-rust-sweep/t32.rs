pub fn split_at_safe(v: &[u8], i: usize) -> (&[u8], &[u8]) {
    v.split_at(i.min(v.len()))
}
