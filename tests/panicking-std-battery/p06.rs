pub fn f(v: &[u8], i: usize) -> (&[u8], &[u8]) {
    v.split_at(i)
}
