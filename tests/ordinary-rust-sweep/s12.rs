pub fn repeat(s: &str, n: usize) -> String {
    s.repeat(n.min(4))
}
