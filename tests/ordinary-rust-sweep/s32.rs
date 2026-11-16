pub fn from_iter_str(v: &[&str]) -> String {
    v.iter().copied().collect()
}
