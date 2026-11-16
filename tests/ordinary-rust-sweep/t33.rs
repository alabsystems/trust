pub fn as_lower(s: &str) -> String {
    s.chars().map(|c| c.to_ascii_lowercase()).collect()
}
