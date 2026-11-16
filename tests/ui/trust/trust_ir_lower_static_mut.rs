//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-verify-timeout-ms=2000
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// The 2 s per-obligation budget (default 20 s) removes most of this file's
// cost, because some engine runs out the budget on an obligation it cannot
// decide. It is safe: every per-function verdict was measured identical at
// 0.5 s, 2 s and 20 s (2026-09-23, 96f2019566). No verdict annotations here: this file
// is in the scorecard's frozen [in-pool] sample, which admits no annotated file.
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
