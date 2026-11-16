#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let mut v = Vec::new(); let mut i = 0; while i < x % 50 { v.push(i * 2); i += 1; } let mut s = 0; for e in &v { s += *e; } s + v.len() as u64 }
