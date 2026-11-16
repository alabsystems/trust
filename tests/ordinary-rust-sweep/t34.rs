pub fn xor_all(v: &[u32]) -> u32 {
    v.iter().fold(0u32, |a, b| a ^ b)
}
