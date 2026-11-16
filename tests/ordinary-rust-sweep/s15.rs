pub fn pair_max(v: &[(u32, u32)]) -> Option<u32> {
    v.iter().map(|p| p.0.max(p.1)).max()
}
