// Accessing a `static mut` is unconditionally unsafe (another thread may be
// mutating it — a data race). Trust does not model it, so it must be CAUGHT
// fail-closed.
//   trustc -Z trust-verify-output=human --crate-type lib mutable_static_caught.rs
#![allow(dead_code)]

static mut COUNTER: u32 = 0;

/// Reads/writes `COUNTER` (a `static mut`) — must be CAUGHT (`[unsafe:mutable-static]`).
pub fn bump() -> u32 {
    unsafe {
        COUNTER = COUNTER.wrapping_add(1);
        COUNTER
    }
}

/// Control: an immutable static is SAFE — must NOT be flagged.
static LIMIT: u32 = 100;
pub fn at_limit(x: u32) -> bool {
    x >= LIMIT
}
