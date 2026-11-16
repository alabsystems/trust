#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let f = x as f64 * 1.5 + 0.25; f as u64 }
