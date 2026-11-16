#[inline(never)] fn a(v: u64) -> u64 { v + 1 } #[inline(never)] fn b(v: u64) -> u64 { v * 2 }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let f: fn(u64) -> u64 = if x & 1 == 0 { a } else { b }; f(x) }
