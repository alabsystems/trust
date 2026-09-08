//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-SM): a LOCAL `static mut` is a MUTABLE module global — the same
//! `GlobalAddr` an immutable static gets, with `mutable: true` and its address
//! in the `&mut` ledger — so a read is a `Load`, `C = v` / `C += v` are
//! `Store`s through it. (A `&raw mut C` / `&mut C` of the static is NOT yet
//! admitted: `reborrow_target` classifies the `Deref { StaticRef }` place as
//! no place, so it keeps `Borrow(&mut non-local place)`.) Every body here
//! carried `StaticRef(mutable static)` before the wave; `strict` turns that
//! into a compile error, so this file is the mutation check.
static mut COUNTER: u32 = 0;
static mut FLAG: bool = false;
static mut TOTAL: i64 = -5;
fn bump() -> u32 {
    unsafe {
        COUNTER += 1;
        COUNTER
    }
}
fn set(v: bool) {
    unsafe {
        FLAG = v;
    }
}
fn get() -> bool {
    unsafe { FLAG }
}
fn add(x: i64) -> i64 {
    unsafe {
        TOTAL = TOTAL + x;
        TOTAL
    }
}
fn main() {
    let a = bump();
    set(true);
    let g = get();
    let t = add(7);
    std::process::exit((a != 1 || !g || t != 2) as i32);
}
