#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let big = u64::MAX - 1000; let y = big + x; y - big + 1 }
