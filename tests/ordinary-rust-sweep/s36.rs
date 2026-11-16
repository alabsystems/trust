pub fn take_while_sum(v: &[u8]) -> u32 {
    v.iter().take_while(|x| **x < 100).map(|x| *x as u32).sum()
}
