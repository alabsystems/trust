pub fn shift(x: u32, k: u32) -> u32 {
    x.checked_shl(k.min(31)).unwrap_or(0)
}
