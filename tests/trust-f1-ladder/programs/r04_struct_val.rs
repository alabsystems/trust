#[derive(Clone, Copy)] struct P { a: u64, b: u64, c: u32 }
#[inline(never)] fn mk(x: u64) -> P { P { a: x + 1, b: x * 2, c: 7 } }
#[inline(never)] fn sum(p: P) -> u64 { p.a + p.b + p.c as u64 }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { sum(mk(x)) }
