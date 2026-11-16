pub fn nth_or(v: &[u32], i: usize, d: u32) -> u32 {
    v.get(i).copied().unwrap_or(d)
}
