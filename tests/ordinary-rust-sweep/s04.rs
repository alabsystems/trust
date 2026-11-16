pub fn parse_or(s: &str, d: u32) -> u32 {
    s.parse::<u32>().unwrap_or(d)
}
