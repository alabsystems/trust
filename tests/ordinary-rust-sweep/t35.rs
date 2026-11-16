pub fn ok_or_zero(r: Result<u32, String>) -> u32 {
    r.unwrap_or(0)
}
