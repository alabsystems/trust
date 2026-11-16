#[derive(Debug)]
pub enum Error {
    Empty,
    TooLarge(usize),
}
pub fn checked_sum(v: &[u32]) -> Result<u32, Error> {
    if v.is_empty() {
        return Err(Error::Empty);
    }
    if v.len() > 1000 {
        return Err(Error::TooLarge(v.len()));
    }
    let mut s = 0u32;
    for x in v {
        s = s.wrapping_add(*x);
    }
    Ok(s)
}
