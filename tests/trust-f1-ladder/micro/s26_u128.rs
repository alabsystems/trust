#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let w = (x as u128) * 0x1_0000_0001u128; (w >> 32) as u64 }
