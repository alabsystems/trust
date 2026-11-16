#[inline(never)] fn h(a: u64) -> u64 { a * 5 + 1 }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { h(x) + h(x + 1) }
