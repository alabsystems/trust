//@ dont-check-compiler-stderr
//@ check-fail
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// RE-PINNED 2026-09-16. This body used to lower "fully" under
// `-Ztrust-ir-lower=strict`, but only because a `&mut` receiver whose borrow
// could not become a pointer was carried into the call AS A VALUE. That edge
// does not type-check — the callee's parameter is a pointer — and it was
// invisible only while declarations wore the v41-outlawed unknown-signature
// spelling, which made the argument/parameter comparison run zero times.
//
// The carrier is now refused for a reference-typed argument, so this body
// honestly reports `Borrow(&mut slot missing)` instead. Carrying a value for a
// `&mut` is the worse half of the bug: a write through it cannot propagate
// back, so a body that lowered only by doing so was never faithfully lowered.
// The fix that would restore full lowering is a real pointer for this borrow,
// which needs the `&mut` slot the message names — not the carrier.
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
    //~^ ERROR could not fully lower this body
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
