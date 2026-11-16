pub fn zip_sum(a: &[u8], b: &[u8]) -> u32 {
    a.iter().zip(b.iter()).map(|(x, y)| *x as u32 + *y as u32).sum()
}
