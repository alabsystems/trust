// Result combinator breadth harvest — Trust 21-lane certifier survey.
// Family: Result::<T,E>::unwrap_or (7 T x 2 E), is_ok/is_err (6 combos),
// ok()/err() (3 combos, Option-returning), method-call unwrap_or (4 combos).

// ---- Set 1: fully-qualified Result::<T,E>::unwrap_or, T x E = {i8,i16,i64,u16,u32,u128,isize} x {u8,i32}

#[inline(never)]
fn uo_i8_u8(r: Result<i8, u8>, d: i8) -> i8 { Result::<i8, u8>::unwrap_or(r, d) }
#[inline(never)]
fn uo_i8_i32(r: Result<i8, i32>, d: i8) -> i8 { Result::<i8, i32>::unwrap_or(r, d) }
#[inline(never)]
fn uo_i16_u8(r: Result<i16, u8>, d: i16) -> i16 { Result::<i16, u8>::unwrap_or(r, d) }
#[inline(never)]
fn uo_i16_i32(r: Result<i16, i32>, d: i16) -> i16 { Result::<i16, i32>::unwrap_or(r, d) }
#[inline(never)]
fn uo_i64_u8(r: Result<i64, u8>, d: i64) -> i64 { Result::<i64, u8>::unwrap_or(r, d) }
#[inline(never)]
fn uo_i64_i32(r: Result<i64, i32>, d: i64) -> i64 { Result::<i64, i32>::unwrap_or(r, d) }
#[inline(never)]
fn uo_u16_u8(r: Result<u16, u8>, d: u16) -> u16 { Result::<u16, u8>::unwrap_or(r, d) }
#[inline(never)]
fn uo_u16_i32(r: Result<u16, i32>, d: u16) -> u16 { Result::<u16, i32>::unwrap_or(r, d) }
#[inline(never)]
fn uo_u32_u8(r: Result<u32, u8>, d: u32) -> u32 { Result::<u32, u8>::unwrap_or(r, d) }
#[inline(never)]
fn uo_u32_i32(r: Result<u32, i32>, d: u32) -> u32 { Result::<u32, i32>::unwrap_or(r, d) }
#[inline(never)]
fn uo_u128_u8(r: Result<u128, u8>, d: u128) -> u128 { Result::<u128, u8>::unwrap_or(r, d) }
#[inline(never)]
fn uo_u128_i32(r: Result<u128, i32>, d: u128) -> u128 { Result::<u128, i32>::unwrap_or(r, d) }
#[inline(never)]
fn uo_isize_u8(r: Result<isize, u8>, d: isize) -> isize { Result::<isize, u8>::unwrap_or(r, d) }
#[inline(never)]
fn uo_isize_i32(r: Result<isize, i32>, d: isize) -> isize { Result::<isize, i32>::unwrap_or(r, d) }

// ---- Set 2: is_ok / is_err at 6 more (T,E) combos

#[inline(never)]
fn isok_u8_u8(r: Result<u8, u8>) -> bool { r.is_ok() }
#[inline(never)]
fn iserr_u8_u8(r: Result<u8, u8>) -> bool { r.is_err() }
#[inline(never)]
fn isok_i32_i64(r: Result<i32, i64>) -> bool { r.is_ok() }
#[inline(never)]
fn iserr_i32_i64(r: Result<i32, i64>) -> bool { r.is_err() }
#[inline(never)]
fn isok_u64_u16(r: Result<u64, u16>) -> bool { r.is_ok() }
#[inline(never)]
fn iserr_u64_u16(r: Result<u64, u16>) -> bool { r.is_err() }
#[inline(never)]
fn isok_i128_u32(r: Result<i128, u32>) -> bool { r.is_ok() }
#[inline(never)]
fn iserr_i128_u32(r: Result<i128, u32>) -> bool { r.is_err() }
#[inline(never)]
fn isok_usize_i8(r: Result<usize, i8>) -> bool { r.is_ok() }
#[inline(never)]
fn iserr_usize_i8(r: Result<usize, i8>) -> bool { r.is_err() }
#[inline(never)]
fn isok_u16_isize(r: Result<u16, isize>) -> bool { r.is_ok() }
#[inline(never)]
fn iserr_u16_isize(r: Result<u16, isize>) -> bool { r.is_err() }

// ---- Set 3: ok() / err() — Option-returning

#[inline(never)]
fn ok_i32_u8(r: Result<i32, u8>) -> Option<i32> { r.ok() }
#[inline(never)]
fn err_i32_u8(r: Result<i32, u8>) -> Option<u8> { r.err() }
#[inline(never)]
fn ok_u64_i16(r: Result<u64, i16>) -> Option<u64> { r.ok() }
#[inline(never)]
fn err_u64_i16(r: Result<u64, i16>) -> Option<i16> { r.err() }
#[inline(never)]
fn ok_usize_i64(r: Result<usize, i64>) -> Option<usize> { r.ok() }
#[inline(never)]
fn err_usize_i64(r: Result<usize, i64>) -> Option<i64> { r.err() }

// ---- Set 4: method-call syntax r.unwrap_or(d), 4 combos

#[inline(never)]
fn uom_i8_u8(r: Result<i8, u8>, d: i8) -> i8 { r.unwrap_or(d) }
#[inline(never)]
fn uom_i64_i32(r: Result<i64, i32>, d: i64) -> i64 { r.unwrap_or(d) }
#[inline(never)]
fn uom_u32_u8(r: Result<u32, u8>, d: u32) -> u32 { r.unwrap_or(d) }
#[inline(never)]
fn uom_isize_i32(r: Result<isize, i32>, d: isize) -> isize { r.unwrap_or(d) }

fn main() {
    let n = std::env::args().count(); // >= 1 at runtime, unknown statically
    let even = n % 2 == 0;

    // Set 1
    let r1: Result<i8, u8> = if even { Ok(n as i8) } else { Err(n as u8) };
    let r2: Result<i8, i32> = if even { Ok(n as i8) } else { Err(n as i32) };
    let r3: Result<i16, u8> = if even { Ok(n as i16) } else { Err(n as u8) };
    let r4: Result<i16, i32> = if even { Ok(n as i16) } else { Err(n as i32) };
    let r5: Result<i64, u8> = if even { Ok(n as i64) } else { Err(n as u8) };
    let r6: Result<i64, i32> = if even { Ok(n as i64) } else { Err(n as i32) };
    let r7: Result<u16, u8> = if even { Ok(n as u16) } else { Err(n as u8) };
    let r8: Result<u16, i32> = if even { Ok(n as u16) } else { Err(n as i32) };
    let r9: Result<u32, u8> = if even { Ok(n as u32) } else { Err(n as u8) };
    let r10: Result<u32, i32> = if even { Ok(n as u32) } else { Err(n as i32) };
    let r11: Result<u128, u8> = if even { Ok(n as u128) } else { Err(n as u8) };
    let r12: Result<u128, i32> = if even { Ok(n as u128) } else { Err(n as i32) };
    let r13: Result<isize, u8> = if even { Ok(n as isize) } else { Err(n as u8) };
    let r14: Result<isize, i32> = if even { Ok(n as isize) } else { Err(n as i32) };

    let mut acc: u128 = 0;
    acc = acc.wrapping_add(uo_i8_u8(r1, 1) as u128);
    acc = acc.wrapping_add(uo_i8_i32(r2, 2) as u128);
    acc = acc.wrapping_add(uo_i16_u8(r3, 3) as u128);
    acc = acc.wrapping_add(uo_i16_i32(r4, 4) as u128);
    acc = acc.wrapping_add(uo_i64_u8(r5, 5) as u128);
    acc = acc.wrapping_add(uo_i64_i32(r6, 6) as u128);
    acc = acc.wrapping_add(uo_u16_u8(r7, 7) as u128);
    acc = acc.wrapping_add(uo_u16_i32(r8, 8) as u128);
    acc = acc.wrapping_add(uo_u32_u8(r9, 9) as u128);
    acc = acc.wrapping_add(uo_u32_i32(r10, 10) as u128);
    acc = acc.wrapping_add(uo_u128_u8(r11, 11));
    acc = acc.wrapping_add(uo_u128_i32(r12, 12));
    acc = acc.wrapping_add(uo_isize_u8(r13, 13) as u128);
    acc = acc.wrapping_add(uo_isize_i32(r14, 14) as u128);

    // Set 2
    let s1: Result<u8, u8> = if even { Ok(n as u8) } else { Err(n as u8) };
    let s2: Result<i32, i64> = if even { Ok(n as i32) } else { Err(n as i64) };
    let s3: Result<u64, u16> = if even { Ok(n as u64) } else { Err(n as u16) };
    let s4: Result<i128, u32> = if even { Ok(n as i128) } else { Err(n as u32) };
    let s5: Result<usize, i8> = if even { Ok(n) } else { Err(n as i8) };
    let s6: Result<u16, isize> = if even { Ok(n as u16) } else { Err(n as isize) };

    let mut b: u32 = 0;
    b += isok_u8_u8(s1) as u32;
    b += iserr_u8_u8(s1) as u32;
    b += isok_i32_i64(s2) as u32;
    b += iserr_i32_i64(s2) as u32;
    b += isok_u64_u16(s3) as u32;
    b += iserr_u64_u16(s3) as u32;
    b += isok_i128_u32(s4) as u32;
    b += iserr_i128_u32(s4) as u32;
    b += isok_usize_i8(s5) as u32;
    b += iserr_usize_i8(s5) as u32;
    b += isok_u16_isize(s6) as u32;
    b += iserr_u16_isize(s6) as u32;

    // Set 3
    let t1: Result<i32, u8> = if even { Ok(n as i32) } else { Err(n as u8) };
    let t2: Result<u64, i16> = if even { Ok(n as u64) } else { Err(n as i16) };
    let t3: Result<usize, i64> = if even { Ok(n) } else { Err(n as i64) };

    let mut c: u32 = 0;
    c += ok_i32_u8(t1).is_some() as u32;
    c += err_i32_u8(t1).is_some() as u32;
    c += ok_u64_i16(t2).is_some() as u32;
    c += err_u64_i16(t2).is_some() as u32;
    c += ok_usize_i64(t3).is_some() as u32;
    c += err_usize_i64(t3).is_some() as u32;

    // Set 4
    acc = acc.wrapping_add(uom_i8_u8(r1, 21) as u128);
    acc = acc.wrapping_add(uom_i64_i32(r6, 22) as u128);
    acc = acc.wrapping_add(uom_u32_u8(r9, 23) as u128);
    acc = acc.wrapping_add(uom_isize_i32(r14, 24) as u128);

    println!("{} {} {}", acc, b, c);
}
