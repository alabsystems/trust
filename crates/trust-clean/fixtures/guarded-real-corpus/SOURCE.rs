pub fn safe_idx(s: &[u32], i: usize) -> u32 { if i < s.len() { s[i] } else { 0 } }
pub fn guarded_add(a: u32, b: u32) -> u32 { if a < 100 && b < 100 { a + b } else { 0 } }
pub fn guarded_div(a: u32, b: u32) -> u32 { if b != 0 { a / b } else { 0 } }
pub fn guarded_sub(a: u32, b: u32) -> u32 { if a >= b { a - b } else { 0 } }
pub fn clamp_idx(s: &[u32]) -> u32 { if s.len() > 3 { s[3] } else { 0 } }
