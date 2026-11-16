pub fn f(x: u32) -> u32 { let mut r = 0; loop { r += 1; if r > x.min(5) { break; } } r }
