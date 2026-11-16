#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { match x & 7 { 0 => 11, 1 => 22, 2 | 3 => 33, 4..=6 => x, _ => 99 } }
