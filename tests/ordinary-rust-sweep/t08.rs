pub fn nonzero(v: &[i32]) -> Vec<i32> {
    v.iter().copied().filter(|x| *x != 0).collect()
}
