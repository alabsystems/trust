pub fn split_once_kv(s: &str) -> Option<(&str, &str)> {
    s.split_once(char::is_whitespace)
}
