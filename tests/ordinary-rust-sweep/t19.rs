pub fn sum_pairs(v: &[(u8, u8)]) -> u32 {
    v.iter().map(|(a, b)| *a as u32 + *b as u32).sum()
}
