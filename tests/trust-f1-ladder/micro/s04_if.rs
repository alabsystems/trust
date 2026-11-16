#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { if x < 5 { 1 } else { 2 } }
