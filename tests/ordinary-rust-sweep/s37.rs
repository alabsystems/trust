pub fn chunk_count(v: &[u32]) -> usize {
    v.chunks(4).count()
}
