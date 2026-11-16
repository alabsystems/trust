pub fn f(v: &[u8], n: usize) -> usize {
    v.chunks(n).count()
}
