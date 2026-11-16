struct P { a: u64, b: u64 }
#[inline(never)] fn bump(p: &mut P, k: u64) { p.a += k; p.b = p.b * 2 + 1; }
#[inline(never)] fn read(p: &P) -> u64 { p.a ^ p.b }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let mut p = P { a: x, b: 3 }; bump(&mut p, 5); bump(&mut p, x); read(&p) }
