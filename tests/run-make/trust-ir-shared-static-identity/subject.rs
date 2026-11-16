// Trust: one actual Rust static must remain one allocation across emitted bodies.
#![allow(dead_code)]

static mut FIRST: u64 = 17;
static mut SECOND: u64 = 17;
static IMMUTABLE: u64 = 17;

#[inline(never)]
pub fn write_first(value: u64) {
    unsafe { FIRST = value }
}

#[inline(never)]
pub fn read_first() -> u64 {
    unsafe { FIRST }
}

#[inline(never)]
pub fn read_first_again() -> u64 {
    unsafe { FIRST }
}

#[inline(never)]
pub fn read_second() -> u64 {
    unsafe { SECOND }
}

#[inline(never)]
pub fn read_immutable() -> u64 {
    IMMUTABLE
}

#[inline(never)]
pub fn read_immutable_again() -> u64 {
    IMMUTABLE
}

#[inline(never)]
pub fn write_then_read(value: u64) -> u64 {
    write_first(value);
    read_first()
}
