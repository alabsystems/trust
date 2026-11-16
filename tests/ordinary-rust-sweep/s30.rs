pub fn fold_min(v: &[i32]) -> i32 {
    v.iter().copied().fold(i32::MAX, i32::min)
}
