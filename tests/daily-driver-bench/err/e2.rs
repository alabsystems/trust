pub fn f(r: Result<u32, ()>) -> u32 { r.unwrap_or(0) }
