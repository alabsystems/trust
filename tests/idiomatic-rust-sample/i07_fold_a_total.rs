pub fn total(v: &[u32]) -> u64 { v.iter().fold(0u64, |a, &x| a + x as u64) }
