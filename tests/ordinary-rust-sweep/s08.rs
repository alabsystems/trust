pub fn last_word(s: &str) -> &str {
    s.rsplit(char::is_whitespace).next().unwrap_or("")
}
