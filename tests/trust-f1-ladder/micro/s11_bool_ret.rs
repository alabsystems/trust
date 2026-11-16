#[inline(never)] fn h(a: u64) -> bool { a & 4 != 0 }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { if h(x) { 9 } else { 4 } }
