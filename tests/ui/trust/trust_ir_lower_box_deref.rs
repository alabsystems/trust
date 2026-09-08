//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-BX): a `Box<T>` is a heap pointer. The data pointer inside the
//! registered `Box(Unique(NonNull(*const T), _), Global)` aggregate is a
//! ledgered pointer, so `*b` is a `Load`, `*b = v` / `*b op= v` are `Store`s,
//! `(*b).f = v` is the struct read-modify-write, and `&*b` / `&mut *b` are the
//! pointer itself. `Box::new` stays an extern callee (its result is the opaque
//! Box aggregate). Every body here carried `Deref(non-borrow ptr)` (or its
//! store/borrow twins) before the wave; `strict` turns that into a compile
//! error, so this file is the mutation check.
struct S {
    a: i64,
    b: i64,
}
fn read(b: Box<i32>) -> i32 {
    *b
}
fn through_ref(b: &Box<i32>) -> i32 {
    **b
}
fn write(mut b: Box<i32>) -> i32 {
    *b = 9;
    *b
}
fn bump(b: &mut Box<u8>) {
    **b += 1;
}
fn local() -> i32 {
    let b = Box::new(7);
    *b + 1
}
fn field(b: Box<S>) -> i64 {
    b.a + (*b).b
}
fn set_field(mut b: Box<S>) -> i64 {
    (*b).a = 5;
    b.b = 6;
    b.a * b.b
}
fn reborrow(b: &mut Box<i32>) -> i32 {
    let r: &mut i32 = &mut **b;
    *r += 1;
    let s: &i32 = &**b;
    *s
}
fn main() {
    let mut x = Box::new(1u8);
    bump(&mut x);
    let mut y = Box::new(41);
    let r = reborrow(&mut y);
    let ok = read(Box::new(3)) == 3
        && through_ref(&Box::new(4)) == 4
        && write(Box::new(0)) == 9
        && local() == 8
        && field(Box::new(S { a: 2, b: 3 })) == 5
        && set_field(Box::new(S { a: 0, b: 0 })) == 30
        && r == 42;
    std::process::exit(!ok as i32);
}
