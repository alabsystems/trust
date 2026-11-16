#[inline(never)] fn sum(s: &[u64]) -> u64 { let mut t = 0; let mut i = 0; while i < s.len() { t += s[i]; i += 1; } t }
#[inline(never)] fn bytes(s: &str) -> u64 { let b = s.as_bytes(); let mut t = 0u64; let mut i = 0; while i < b.len() { t += b[i] as u64; i += 1; } t }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let a = [x, 2, 3, 4]; let n = (x % 5) as usize; sum(&a[..n.min(4)]) + bytes("hello") + "wörld".len() as u64 }
