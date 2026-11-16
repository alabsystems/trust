#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let k = x + 1; let f = |y: u64| y * k + 2; f(3) + f(4) }
