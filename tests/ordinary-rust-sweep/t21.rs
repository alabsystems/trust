pub fn find_idx(v: &[u8], t: u8) -> Option<usize> {
    v.iter().position(|x| *x == t)
}
