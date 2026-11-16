pub fn windows2(v: &[u32]) -> usize {
    v.windows(2).filter(|w| w[0] <= w[1]).count()
}
