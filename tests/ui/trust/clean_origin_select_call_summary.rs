//@ needs-trust-verify
//@ edition: 2021
//@ revisions: bound literal assert wrong_arm wrong_order
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[bound] check-pass
//@[literal] check-pass
//@[assert] check-pass
//@[wrong_arm] check-fail
//@[wrong_order] check-fail
//! **A caller of a SELECT-shaped island `def` gets its value semantics
//! (Trust, 2026-09-28).**
//!
//! `def min2 a b := if a < b then a else b` is emitted as the four-block
//! compare-branch-move diamond, gate-checked against the kernel `ite`. Callers
//! got no model of its result: `fn f(a, b) -> u64 ensures result <= a
//! { min2(a, b) }` stayed unproved, while the same callee written in Rust proved.
//! That was the missing "select summary lane" recorded at the shape's arm in
//! `clean_origin_call_record_of_record`. A parameter-armed select (a parameter or
//! a numeral on the comparison's right) now carries `_0 == ite(a ⊲ R, t, e)`,
//! through the same constructor as the projection's `_0 == arg_i`.
//!
//! * `bound`, `literal`, `assert`: POSITIVE. The `ensures` or `assert!` holds.
//! * `wrong_arm`: `ensures result <= b` is true too; `ensures result == a` is
//!   not (for `a > b`), and must be refuted.
//! * `wrong_order`: the summary must not read the arms backwards.
//!   `max2 a b := if a < b then b else a` with the claim `result <= a`, which is
//!   false for `a < b`.

#[cfg(any(bound, assert, wrong_arm))]
clean {
    def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
}

#[cfg(bound)]
pub fn call_min(a: u64, b: u64) -> u64
    ensures result <= a && result <= b
{
    min2(a, b)
}

#[cfg(literal)]
clean {
    def below10 (x : UInt32) (d : UInt32) : UInt32 := if x < 10 then x else d
}

#[cfg(literal)]
pub fn call_below(x: u32) -> u32
    ensures result < 10 || result == 0
{
    below10(x, 0)
}

#[cfg(assert)]
pub fn call_min_assert(a: u64, b: u64) -> u64 {
    let r = min2(a, b);
    assert!(r <= a);
    r
}

#[cfg(wrong_arm)]
pub fn call_min(a: u64, b: u64) -> u64
    ensures result == a
{
    //[wrong_arm]~^^^ ERROR Trust
    min2(a, b)
}

#[cfg(wrong_order)]
clean {
    def max2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then b else a
}

#[cfg(wrong_order)]
pub fn call_max(a: u64, b: u64) -> u64
    ensures result <= a
{
    //[wrong_order]~^^^ ERROR Trust
    max2(a, b)
}
