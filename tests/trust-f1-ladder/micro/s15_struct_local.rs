struct P { a: u64, b: u64 }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let p = P { a: x + 1, b: x * 2 }; p.a ^ p.b }
