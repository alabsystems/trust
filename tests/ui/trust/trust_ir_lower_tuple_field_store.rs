//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-TF): `t.1 = v` on an SSA-bound TUPLE local is an `InsertField`
//! over the tuple value (the struct-local store's scalar-leaf posture). Every
//! body here carried `Assign(non-local place)` before the wave; `strict` turns
//! that into a compile error, so this file is the mutation check.
fn swap_second(x: u32) -> (u32, u32) {
    let mut t = (1u32, 2u32);
    t.1 = x;
    t.0 = t.1 + 1;
    t
}
fn flag(b: bool) -> (bool, i64) {
    let mut t = (false, -3i64);
    t.0 = b;
    t.1 = 9;
    t
}
fn main() {
    let (a, b) = swap_second(5);
    let (c, d) = flag(true);
    std::process::exit(!(a == 6 && b == 5 && c && d == 9) as i32);
}
