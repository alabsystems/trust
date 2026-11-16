pub fn trunc(s: &str, n: usize) -> &str {
    let n = n.min(s.len());
    match s.get(..n) {
        Some(t) => t,
        None => s,
    }
}
