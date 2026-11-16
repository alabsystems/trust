pub fn count_upper(s: &str) -> usize {
    s.chars().filter(|c| c.is_uppercase()).count()
}
