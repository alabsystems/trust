pub fn opt_q(a: Option<u32>, b: Option<u32>) -> Option<u32> {
    Some(a?.saturating_add(b?))
}
