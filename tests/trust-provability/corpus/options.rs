//! Option/Result plumbing — pervasive in real Rust.
pub fn first_digit(x: u32) -> Option<u32> { if x == 0 { None } else { Some(x % 10) } }
pub fn checked(a: u32, b: u32) -> Option<u32> { a.checked_add(b) }
pub fn or_default(v: Option<u32>) -> u32 { match v { Some(x) => x, None => 0 } }
pub fn parse_flag(b: u8) -> Result<bool, u8> { match b { 0 => Ok(false), 1 => Ok(true), other => Err(other) } }
