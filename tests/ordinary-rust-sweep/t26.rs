pub fn deep(o: Option<Option<u32>>) -> u32 {
    o.flatten().unwrap_or(0)
}
