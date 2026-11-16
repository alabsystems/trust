pub fn is_pal(s: &[u8]) -> bool {
    let n = s.len();
    (0..n / 2).all(|i| s[i] == s[n - 1 - i])
}
