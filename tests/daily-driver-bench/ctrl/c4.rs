pub fn f(n: u32) -> u32 { let mut a = 0u32; for i in 0..n.min(10) { a = a.wrapping_add(i); } a }
