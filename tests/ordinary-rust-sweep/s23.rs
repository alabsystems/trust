pub fn is_sorted(v: &[u32]) -> bool {
    v.windows(2).all(|w| w[0] <= w[1])
}
