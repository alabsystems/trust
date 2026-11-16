#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let a = x / 3 + (x ^ 0x55) * 2; let b = (a << 3) | (x & 7); b - (x >> 1) + 11 }
