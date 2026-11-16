#[inline(never)] fn h(a: u64, b: u64) -> u64 { a * b + a }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { h(x, 3) }
