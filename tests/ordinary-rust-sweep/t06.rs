pub fn scale(v: &mut [u16], k: u16) {
    for x in v.iter_mut() {
        *x = x.saturating_mul(k);
    }
}
