pub fn sum_u64(v: &[u32]) -> u64 {
    v.iter().map(|x| *x as u64).sum()
}
