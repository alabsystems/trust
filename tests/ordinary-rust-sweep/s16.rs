pub fn opt_chain(a: Option<u32>) -> Option<u32> {
    a.map(|x| x.saturating_mul(2)).filter(|x| *x > 3)
}
