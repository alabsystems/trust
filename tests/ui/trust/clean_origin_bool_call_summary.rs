//@ needs-trust-verify
//@ edition: 2021
//@ revisions: cmp not conn guard wrong_cmp wrong_conn
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[cmp] check-pass
//@[not] check-pass
//@[conn] check-pass
//@[guard] check-pass
//@[wrong_cmp] check-fail
//@[wrong_conn] check-fail
//! **A caller of a `Bool`-valued island `def` gets its value (Trust, 2026-09-28).**
//!
//! The W6 shapes: a comparison of two parameters returned as `Bool`
//! (`def lt a b := a < b`), `Bool.not`, and `and`/`or` of two `Bool` parameters.
//! Each is emitted as a one-block body (`_0 = Lt(a, b)`, `_0 = Not(b)`,
//! `_0 = BitAnd(a, b)`) and gate-checked. Callers had no model of the result,
//! and each shape's arm in `clean_origin_call_record_of_record` recorded that.
//! Each now carries a `Bool` equality (`_0 == (a < b)`, `_0 == ¬b`,
//! `_0 == (a ∧ b)`).
//!
//! * `cmp`, `not`, `conn`: POSITIVE, an `ensures` restating the island value.
//! * `guard`: the summary discharges a SAFETY row. The island comparison guards
//!   an index.
//! * `wrong_cmp`: `ensures result == (a <= b)` over `a < b` is false for `a == b`.
//! * `wrong_conn`: `ensures result == (a || b)` over `a && b`.

#[cfg(any(cmp, guard, wrong_cmp))]
clean {
    def lt (a : UInt64) (b : UInt64) : Bool := a < b
}

#[cfg(cmp)]
pub fn call_lt(a: u64, b: u64) -> bool
    ensures result == (a < b)
{
    lt(a, b)
}

#[cfg(not)]
clean {
    def neg (b : Bool) : Bool := not b
}

#[cfg(not)]
pub fn call_neg(b: bool) -> bool
    ensures result == !b
{
    neg(b)
}

#[cfg(any(conn, wrong_conn))]
clean {
    def both (a : Bool) (b : Bool) : Bool := a && b
}

#[cfg(conn)]
pub fn call_both(a: bool, b: bool) -> bool
    ensures result == (a && b)
{
    both(a, b)
}

#[cfg(guard)]
pub fn pick(table: [u32; 4], i: u64) -> u32 {
    if lt(i, 4) { table[i as usize] } else { 0 }
}

#[cfg(wrong_cmp)]
pub fn call_lt(a: u64, b: u64) -> bool
    ensures result == (a <= b)
{
    //[wrong_cmp]~^^^ ERROR Trust
    lt(a, b)
}

#[cfg(wrong_conn)]
pub fn call_both(a: bool, b: bool) -> bool
    ensures result == (a || b)
{
    //[wrong_conn]~^^^ ERROR Trust
    both(a, b)
}
