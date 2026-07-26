// Assert-guarded arithmetic — real trustc MIR. Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
pub fn checked_id(x: u64) -> u64 { assert!(x < 1000000000); x }
pub fn bounded_double(x: u64) -> u64 { assert!(x < 1000000000); x + x }
pub fn bounded_sum(a: u64, b: u64) -> u64 { assert!(a < 1000000000); assert!(b < 1000000000); a + b }
