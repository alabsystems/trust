#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { if x < 2 { 10 } else if x & 1 == 0 { if x > 100 { x - 100 } else { x + 1 } } else { x * 3 } }
