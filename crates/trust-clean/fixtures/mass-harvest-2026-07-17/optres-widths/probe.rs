#[inline(never)]
pub fn opt_is_some_i8(o: &Option<i8>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_i8(o: &Option<i8>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_i8(r: &Result<i8, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_i8(r: &Result<i8, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_i16(o: &Option<i16>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_i16(o: &Option<i16>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_i16(r: &Result<i16, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_i16(r: &Result<i16, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_i32(o: &Option<i32>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_i32(o: &Option<i32>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_i32(r: &Result<i32, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_i32(r: &Result<i32, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_i64(o: &Option<i64>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_i64(o: &Option<i64>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_i64(r: &Result<i64, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_i64(r: &Result<i64, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_i128(o: &Option<i128>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_i128(o: &Option<i128>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_i128(r: &Result<i128, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_i128(r: &Result<i128, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_isize(o: &Option<isize>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_isize(o: &Option<isize>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_isize(r: &Result<isize, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_isize(r: &Result<isize, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_u8(o: &Option<u8>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_u8(o: &Option<u8>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_u8(r: &Result<u8, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_u8(r: &Result<u8, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_u16(o: &Option<u16>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_u16(o: &Option<u16>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_u16(r: &Result<u16, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_u16(r: &Result<u16, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_u32(o: &Option<u32>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_u32(o: &Option<u32>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_u32(r: &Result<u32, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_u32(r: &Result<u32, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_u64(o: &Option<u64>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_u64(o: &Option<u64>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_u64(r: &Result<u64, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_u64(r: &Result<u64, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_u128(o: &Option<u128>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_u128(o: &Option<u128>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_u128(r: &Result<u128, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_u128(r: &Result<u128, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn opt_is_some_usize(o: &Option<usize>) -> bool { Option::is_some(o) }
#[inline(never)]
pub fn opt_is_none_usize(o: &Option<usize>) -> bool { Option::is_none(o) }
#[inline(never)]
pub fn res_is_ok_usize(r: &Result<usize, u8>) -> bool { Result::is_ok(r) }
#[inline(never)]
pub fn res_is_err_usize(r: &Result<usize, u8>) -> bool { Result::is_err(r) }

#[inline(never)]
pub fn mcall_opt_is_some_i32(o: Option<i32>) -> bool { o.is_some() }

#[inline(never)]
pub fn mcall_opt_is_some_u64(o: Option<u64>) -> bool { o.is_some() }

#[inline(never)]
pub fn mcall_opt_is_some_i128(o: Option<i128>) -> bool { o.is_some() }

#[inline(never)]
pub fn mcall_opt_is_some_usize(o: Option<usize>) -> bool { o.is_some() }

fn main() {
    let n = std::env::args().count();
    let mut acc = 0usize;
    let o_i8: Option<i8> = if n > 1 { Some(n as i8) } else { None };
    let r_i8: Result<i8, u8> = if n > 2 { Ok(n as i8) } else { Err(n as u8) };
    acc += opt_is_some_i8(&o_i8) as usize;
    acc += opt_is_none_i8(&o_i8) as usize;
    acc += res_is_ok_i8(&r_i8) as usize;
    acc += res_is_err_i8(&r_i8) as usize;
    let o_i16: Option<i16> = if n > 1 { Some(n as i16) } else { None };
    let r_i16: Result<i16, u8> = if n > 2 { Ok(n as i16) } else { Err(n as u8) };
    acc += opt_is_some_i16(&o_i16) as usize;
    acc += opt_is_none_i16(&o_i16) as usize;
    acc += res_is_ok_i16(&r_i16) as usize;
    acc += res_is_err_i16(&r_i16) as usize;
    let o_i32: Option<i32> = if n > 1 { Some(n as i32) } else { None };
    let r_i32: Result<i32, u8> = if n > 2 { Ok(n as i32) } else { Err(n as u8) };
    acc += opt_is_some_i32(&o_i32) as usize;
    acc += opt_is_none_i32(&o_i32) as usize;
    acc += res_is_ok_i32(&r_i32) as usize;
    acc += res_is_err_i32(&r_i32) as usize;
    let o_i64: Option<i64> = if n > 1 { Some(n as i64) } else { None };
    let r_i64: Result<i64, u8> = if n > 2 { Ok(n as i64) } else { Err(n as u8) };
    acc += opt_is_some_i64(&o_i64) as usize;
    acc += opt_is_none_i64(&o_i64) as usize;
    acc += res_is_ok_i64(&r_i64) as usize;
    acc += res_is_err_i64(&r_i64) as usize;
    let o_i128: Option<i128> = if n > 1 { Some(n as i128) } else { None };
    let r_i128: Result<i128, u8> = if n > 2 { Ok(n as i128) } else { Err(n as u8) };
    acc += opt_is_some_i128(&o_i128) as usize;
    acc += opt_is_none_i128(&o_i128) as usize;
    acc += res_is_ok_i128(&r_i128) as usize;
    acc += res_is_err_i128(&r_i128) as usize;
    let o_isize: Option<isize> = if n > 1 { Some(n as isize) } else { None };
    let r_isize: Result<isize, u8> = if n > 2 { Ok(n as isize) } else { Err(n as u8) };
    acc += opt_is_some_isize(&o_isize) as usize;
    acc += opt_is_none_isize(&o_isize) as usize;
    acc += res_is_ok_isize(&r_isize) as usize;
    acc += res_is_err_isize(&r_isize) as usize;
    let o_u8: Option<u8> = if n > 1 { Some(n as u8) } else { None };
    let r_u8: Result<u8, u8> = if n > 2 { Ok(n as u8) } else { Err(n as u8) };
    acc += opt_is_some_u8(&o_u8) as usize;
    acc += opt_is_none_u8(&o_u8) as usize;
    acc += res_is_ok_u8(&r_u8) as usize;
    acc += res_is_err_u8(&r_u8) as usize;
    let o_u16: Option<u16> = if n > 1 { Some(n as u16) } else { None };
    let r_u16: Result<u16, u8> = if n > 2 { Ok(n as u16) } else { Err(n as u8) };
    acc += opt_is_some_u16(&o_u16) as usize;
    acc += opt_is_none_u16(&o_u16) as usize;
    acc += res_is_ok_u16(&r_u16) as usize;
    acc += res_is_err_u16(&r_u16) as usize;
    let o_u32: Option<u32> = if n > 1 { Some(n as u32) } else { None };
    let r_u32: Result<u32, u8> = if n > 2 { Ok(n as u32) } else { Err(n as u8) };
    acc += opt_is_some_u32(&o_u32) as usize;
    acc += opt_is_none_u32(&o_u32) as usize;
    acc += res_is_ok_u32(&r_u32) as usize;
    acc += res_is_err_u32(&r_u32) as usize;
    let o_u64: Option<u64> = if n > 1 { Some(n as u64) } else { None };
    let r_u64: Result<u64, u8> = if n > 2 { Ok(n as u64) } else { Err(n as u8) };
    acc += opt_is_some_u64(&o_u64) as usize;
    acc += opt_is_none_u64(&o_u64) as usize;
    acc += res_is_ok_u64(&r_u64) as usize;
    acc += res_is_err_u64(&r_u64) as usize;
    let o_u128: Option<u128> = if n > 1 { Some(n as u128) } else { None };
    let r_u128: Result<u128, u8> = if n > 2 { Ok(n as u128) } else { Err(n as u8) };
    acc += opt_is_some_u128(&o_u128) as usize;
    acc += opt_is_none_u128(&o_u128) as usize;
    acc += res_is_ok_u128(&r_u128) as usize;
    acc += res_is_err_u128(&r_u128) as usize;
    let o_usize: Option<usize> = if n > 1 { Some(n as usize) } else { None };
    let r_usize: Result<usize, u8> = if n > 2 { Ok(n as usize) } else { Err(n as u8) };
    acc += opt_is_some_usize(&o_usize) as usize;
    acc += opt_is_none_usize(&o_usize) as usize;
    acc += res_is_ok_usize(&r_usize) as usize;
    acc += res_is_err_usize(&r_usize) as usize;
    acc += mcall_opt_is_some_i32(o_i32) as usize;
    acc += mcall_opt_is_some_u64(o_u64) as usize;
    acc += mcall_opt_is_some_i128(o_i128) as usize;
    acc += mcall_opt_is_some_usize(o_usize) as usize;
    println!("{}", acc);
}
