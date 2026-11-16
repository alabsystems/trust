#[inline(never)] fn h(a: i64) -> i64 { if a < 100 { a - 200 } else { a >> 2 } }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { h(x as i64) as u64 }
