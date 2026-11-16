#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { ((x << 3) | (x & 7)) ^ (x >> 1) }
