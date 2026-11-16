#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let b = Box::new(x + 1); let c = Box::new([x, 2, 3]); *b + c[0] + c[2] }
