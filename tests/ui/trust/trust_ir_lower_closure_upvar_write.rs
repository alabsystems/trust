//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-CX): a write to a captured upvar inside an `FnMut` closure body
//! (`sum = sum + i`, `c += 1`) goes THROUGH the captured `&mut T` pointer in
//! the env tuple (or replaces a by-value element and writes the tuple back),
//! and the enclosing body promotes the locals a closure literal captures by
//! `&mut`, exactly as any other `&mut` borrow does. Every body here carried
//! `Assign(non-local place)` / `AssignOp(non-local place)` (closure) or
//! `Borrow(&mut unpromoted local)` (caller) before the wave; `strict` turns
//! that into a compile error, so this file is the mutation check.
fn run(mut it: impl FnMut(isize)) {
    it(1);
    it(2);
}
fn total() -> isize {
    let mut sum: isize = 0;
    run(|i| {
        sum = sum + i;
    });
    sum
}
fn count() -> u8 {
    let mut c = 0u8;
    run(|_| c += 1);
    c
}
fn main() {
    let ok = total() == 3 && count() == 2;
    std::process::exit(!ok as i32);
}
