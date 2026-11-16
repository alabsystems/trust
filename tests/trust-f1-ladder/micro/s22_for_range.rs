#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let mut s = 0; for i in 0..x { s ^= i; } s }
