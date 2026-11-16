//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-CV): a NON-CAPTURING closure literal in value position is the
//! unit ZST it is (`Const { Unit, PhantomData }`, the seed the call-arg lane
//! already mints), its type maps to `Unit` (the oracle's spelling), and a call
//! through the local resolves by the closure type with the unit env. Every
//! body here carried `Closure(value position)` (+ `Ty` on the local's type)
//! before the wave; `strict` turns that into a compile error, so this file is
//! the mutation check.
fn bound() -> i32 {
    let f = || 42;
    f()
}
fn with_arg(x: i32) -> i32 {
    let g = |a: i32| a + 1;
    g(x) + g(1)
}
fn two(x: u8) -> u8 {
    let add = |a: u8, b: u8| a.wrapping_add(b);
    let dbl = |a: u8| a.wrapping_mul(2);
    add(dbl(x), 1)
}
fn main() {
    let ok = bound() == 42 && with_arg(5) == 8 && two(3) == 7;
    std::process::exit(!ok as i32);
}
