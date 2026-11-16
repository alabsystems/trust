#[inline(never)] fn h(a: u32) -> u32 { a * 7 + 3 }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { h(x as u32) as u64 }
