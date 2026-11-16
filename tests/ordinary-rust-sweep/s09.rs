pub fn dedup_len(v: &mut Vec<u32>) -> usize {
    v.dedup();
    v.len()
}
