pub fn count_ge(v: &[i16], t: i16) -> usize {
    v.iter().filter(|x| **x >= t).count()
}
