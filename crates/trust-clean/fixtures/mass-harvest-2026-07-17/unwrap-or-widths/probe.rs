// unwrap_or payload-extract lane width-generality probe.
// Option::<T>::unwrap_or for all 12 int widths, Result::<T,u8>::unwrap_or for 5 widths,
// plus 3 method-call-form wrappers.

#[inline(never)]
pub fn opt_unwrap_or_i8(o: Option<i8>, d: i8) -> i8 {
    Option::<i8>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_i16(o: Option<i16>, d: i16) -> i16 {
    Option::<i16>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_i32(o: Option<i32>, d: i32) -> i32 {
    Option::<i32>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_i64(o: Option<i64>, d: i64) -> i64 {
    Option::<i64>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_i128(o: Option<i128>, d: i128) -> i128 {
    Option::<i128>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_isize(o: Option<isize>, d: isize) -> isize {
    Option::<isize>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_u8(o: Option<u8>, d: u8) -> u8 {
    Option::<u8>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_u16(o: Option<u16>, d: u16) -> u16 {
    Option::<u16>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_u32(o: Option<u32>, d: u32) -> u32 {
    Option::<u32>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_u64(o: Option<u64>, d: u64) -> u64 {
    Option::<u64>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_u128(o: Option<u128>, d: u128) -> u128 {
    Option::<u128>::unwrap_or(o, d)
}
#[inline(never)]
pub fn opt_unwrap_or_usize(o: Option<usize>, d: usize) -> usize {
    Option::<usize>::unwrap_or(o, d)
}

#[inline(never)]
pub fn res_unwrap_or_i8(r: Result<i8, u8>, d: i8) -> i8 {
    Result::<i8, u8>::unwrap_or(r, d)
}
#[inline(never)]
pub fn res_unwrap_or_i32(r: Result<i32, u8>, d: i32) -> i32 {
    Result::<i32, u8>::unwrap_or(r, d)
}
#[inline(never)]
pub fn res_unwrap_or_u64(r: Result<u64, u8>, d: u64) -> u64 {
    Result::<u64, u8>::unwrap_or(r, d)
}
#[inline(never)]
pub fn res_unwrap_or_usize(r: Result<usize, u8>, d: usize) -> usize {
    Result::<usize, u8>::unwrap_or(r, d)
}
#[inline(never)]
pub fn res_unwrap_or_i128(r: Result<i128, u8>, d: i128) -> i128 {
    Result::<i128, u8>::unwrap_or(r, d)
}

// Method-call form wrappers.
#[inline(never)]
pub fn meth_unwrap_or_i32(o: Option<i32>, d: i32) -> i32 {
    o.unwrap_or(d)
}
#[inline(never)]
pub fn meth_unwrap_or_u64(o: Option<u64>, d: u64) -> u64 {
    o.unwrap_or(d)
}
#[inline(never)]
pub fn meth_unwrap_or_usize(o: Option<usize>, d: usize) -> usize {
    o.unwrap_or(d)
}

fn main() {
    let n = std::env::args().count();
    let mut acc: i128 = 0;

    acc += opt_unwrap_or_i8(Some(n as i8), (n + 1) as i8) as i128;
    acc += opt_unwrap_or_i16(Some(n as i16), (n + 1) as i16) as i128;
    acc += opt_unwrap_or_i32(Some(n as i32), (n + 1) as i32) as i128;
    acc += opt_unwrap_or_i64(Some(n as i64), (n + 1) as i64) as i128;
    acc += opt_unwrap_or_i128(Some(n as i128), (n + 1) as i128);
    acc += opt_unwrap_or_isize(Some(n as isize), (n + 1) as isize) as i128;
    acc += opt_unwrap_or_u8(Some(n as u8), (n + 1) as u8) as i128;
    acc += opt_unwrap_or_u16(Some(n as u16), (n + 1) as u16) as i128;
    acc += opt_unwrap_or_u32(Some(n as u32), (n + 1) as u32) as i128;
    acc += opt_unwrap_or_u64(Some(n as u64), (n + 1) as u64) as i128;
    acc += opt_unwrap_or_u128(Some(n as u128), (n + 1) as u128) as i128;
    acc += opt_unwrap_or_usize(Some(n), n + 1) as i128;

    acc += res_unwrap_or_i8(Ok(n as i8), (n + 1) as i8) as i128;
    acc += res_unwrap_or_i32(Err(n as u8), (n + 1) as i32) as i128;
    acc += res_unwrap_or_u64(Ok(n as u64), (n + 1) as u64) as i128;
    acc += res_unwrap_or_usize(Err(n as u8), n + 1) as i128;
    acc += res_unwrap_or_i128(Ok(n as i128), (n + 1) as i128);

    acc += meth_unwrap_or_i32(Some(n as i32), (n + 1) as i32) as i128;
    acc += meth_unwrap_or_u64(None, (n + 1) as u64) as i128;
    acc += meth_unwrap_or_usize(Some(n), n + 1) as i128;

    println!("{}", acc);
}
