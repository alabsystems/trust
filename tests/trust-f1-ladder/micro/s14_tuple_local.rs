#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let t = (x + 1, x * 2); t.0 ^ t.1 }
