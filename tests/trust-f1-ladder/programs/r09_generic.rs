#[inline(never)] fn pick<T: Copy>(c: bool, a: T, b: T) -> T { if c { a } else { b } }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let a = pick(x > 5, x, 5u64); let b = pick(x & 1 == 0, 2u8, 9u8); a + b as u64 }
