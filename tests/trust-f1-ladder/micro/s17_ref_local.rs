#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let mut a = x; { let r = &mut a; *r += 5; } a }
