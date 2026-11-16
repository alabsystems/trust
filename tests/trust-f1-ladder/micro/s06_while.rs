#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let mut s = 0u64; let mut i = 0u64; while i < x { s += i; i += 1; } s }
