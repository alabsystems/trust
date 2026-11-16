pub fn trim_parse(s: &str) -> Option<i64> {
    s.trim().parse::<i64>().ok()
}
