pub fn ratio(a: u32, b: u32) -> Option<u32> {
    if b == 0 { None } else { Some(a / b) }
}
