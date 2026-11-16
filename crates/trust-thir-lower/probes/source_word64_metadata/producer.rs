#![crate_type = "lib"]
#[inline(never)]
pub fn identity(x: u64) -> u64 {
    x
}
#[inline(never)]
pub fn double(x: u64) -> u64 {
    x.wrapping_add(x)
}
#[inline(never)]
pub fn pair(x: u64, y: u64) -> u64 {
    x.wrapping_add(y)
}
#[inline(never)]
pub fn statements(x: u64) -> u64 {
    let y = x;
    y
}

// A legacy MIR-exported refusal must survive the widened producer inventory.
#[inline]
#[track_caller]
pub fn located(x: u64) -> u64 { x }
