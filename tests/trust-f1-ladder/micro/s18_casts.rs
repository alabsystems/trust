#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { (x as u8 as u64) + (x as i8 as i64 as u64) + (x as u16 as u64) }
