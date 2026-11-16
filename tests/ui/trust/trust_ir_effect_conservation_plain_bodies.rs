//@ check-pass
//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! The effect-conservation gate's NEGATIVE control: bodies whose trust-ir carries every effect
//! of rustc's MIR stay strict-clean — calls (foreign, local, through a static), a store through
//! a `&mut` parameter, a store to a `static`, `while` and integer-range `for` loops whose calls
//! are in the loop body, a value moved on rather than dropped, and plain arithmetic. The range
//! loop's `IntoIterator::into_iter` / `Iterator::next` calls are the gate's audited
//! equivalence (`Equivalence::RangeIntoIter` / `RangeNext`): effect-free, panic-free, and the
//! iterator is the body's own local.

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

pub static mut LAST: i32 = 0;

#[inline(never)]
pub fn close_ret(fd: i32) -> i32 {
    unsafe { close(fd) }
}

pub fn record(fd: i32) {
    unsafe { LAST = fd };
}

pub fn store_through(p: &mut i32, fd: i32) {
    *p = close_ret(fd);
}

pub fn while_close(lo: i32, hi: i32) {
    let mut fd = lo;
    while fd < hi {
        close_ret(fd);
        fd += 1;
    }
}

pub fn for_close(lo: i32, hi: i32) {
    for fd in lo..hi {
        unsafe { close(fd) };
    }
}

pub fn max3(a: i64, b: i64, c: i64) -> i64 {
    let m = if a > b { a } else { b };
    if m > c { m } else { c }
}

pub fn sum_to(n: u32) -> u32 {
    let mut i = 0u32;
    let mut s = 0u32;
    while i < n {
        s = s.wrapping_add(i);
        i += 1;
    }
    s
}
