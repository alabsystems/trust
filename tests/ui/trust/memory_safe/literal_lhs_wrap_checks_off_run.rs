//@ revisions: ens idx
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=off
//@[ens] run-pass
//@[idx] run-fail
//@[idx] error-pattern: index out of bounds: the len is 8 but the index is 18446744073709551615
//@ ignore-emscripten no processes
//! The runtime WITNESS for `literal_lhs_wrap_checks_off.rs` (BARE-BINOP-LITERAL-LHS-WIDTH-1):
//! the same liars and the same `idx`, built with verification OFF and overflow checks
//! OFF. A plain `Add`/`Sub` with a literal LEFT operand wraps at its own type's width, so
//! every liar returns a value its `ensures` excludes (`ens`), and `idx(&a, i32::MAX)`
//! reaches `a[(x - n) as usize]` with `n == i32::MIN` (`idx`). Before the fix the
//! sibling's `liars` revision PROVED every one of those postconditions and its `idx`
//! revision PROVED the bounds row.
//!
//! MEASURED 2026-10-13 with these flags plus `--cfg <revision>` on
//! `scratchpad/stage1-w25f` (the wave-25 stage 1, tree of `a971311ee2`) and on stock
//! `rustup run stable rustc` (the `ensures` clauses removed): `ens` exits 0 (every
//! assertion below holds) and `idx` panics with the pattern above, exit 101, on both. The
//! binary does not depend on the verifier, so the fix does not change it; the file pins
//! the fact the sibling's annotations rest on.

#[inline(never)]
pub fn inc1(x: i32) -> i32
    ensures result > x
{
    1 + x
}

#[inline(never)]
pub fn h_lie(x: i8) -> i8
    ensures x <= 27 || result > 0
{
    100 + x
}

#[inline(never)]
pub fn s_lie(x: i32) -> i32
    ensures x <= 0 || result < 0
{
    -2147483647 - x
}

#[inline(never)]
pub fn neg0(x: i32) -> i32
    ensures x >= 0 || result > 0
{
    0 - x
}

#[inline(never)]
pub fn idx(a: &[u8; 8], x: i32) -> u8 {
    let n = 1 + x;
    if n > x { 0 } else { a[(x - n) as usize] }
}

fn main() {
    use std::hint::black_box;
    if cfg!(ens) {
        assert_eq!(inc1(black_box(i32::MAX)), i32::MIN);
        assert_eq!(h_lie(black_box(100)), -56);
        assert_eq!(s_lie(black_box(2)), i32::MAX);
        assert_eq!(neg0(black_box(i32::MIN)), i32::MIN);
        // Away from the wrap, each really is the mathematical value.
        assert_eq!(inc1(black_box(5)), 6);
        assert_eq!(idx(&[7u8; 8], black_box(5)), 0);
    } else {
        println!("{}", idx(&[7u8; 8], black_box(i32::MAX)));
    }
}
