#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let mut i = x; let mut n = 0; loop { if i <= 1 { break; } i = if i & 1 == 0 { i >> 1 } else { i * 3 + 1 }; n += 1; } n }
