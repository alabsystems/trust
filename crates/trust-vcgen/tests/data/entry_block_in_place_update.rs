pub fn f(mut n: u32, a: &[u8; 10]) -> u8 { n /= 3; if n < 10 { a[n as usize] } else { 0 } }
