pub fn to_pairs(v: &[u32]) -> Vec<(usize, u32)> {
    v.iter().copied().enumerate().collect()
}
