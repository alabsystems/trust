#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { if x != 0 { 1000 / x } else { 0 } }
