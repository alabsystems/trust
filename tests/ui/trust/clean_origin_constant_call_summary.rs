//@ needs-trust-verify
//@ edition: 2021
//@ revisions: nullary with_params wrong_value
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[nullary] check-pass
//@[with_params] check-pass
//@[wrong_value] check-fail
//! **A caller of a CONSTANT island `def` gets its value (Trust, 2026-09-28).**
//!
//! `def seven : UInt64 := 7` is emitted as `_0 = const 7_u64; return` and
//! gate-checked against the kernel numeral (§6f landing 2). Its callers had no
//! model of the result. The shape's arm in `clean_origin_call_record_of_record`
//! named the caller summary as a separate increment with its own verify-on
//! fixture: this is that increment and this fixture. The summary is `_0 == 7`,
//! through the same constructor as the projection's.
//!
//! * `nullary`, `with_params`: POSITIVE. A constant at any arity; its parameters
//!   are unread.
//! * `wrong_value`: the NEGATIVE. The summary must carry the numeral, not bless
//!   the claim.

#[cfg(any(nullary, wrong_value))]
clean {
    def seven : UInt64 := 7
}

#[cfg(nullary)]
pub fn call_seven() -> u64
    ensures result == 7
{
    seven()
}

#[cfg(with_params)]
clean {
    def forty (a : UInt32) (b : UInt32) : UInt32 := 40
}

#[cfg(with_params)]
pub fn call_forty(a: u32) -> u32
    ensures result == 41
{
    forty(a, a) + 1
}

#[cfg(wrong_value)]
pub fn call_seven() -> u64
    ensures result == 8
{
    //[wrong_value]~^^^ ERROR Trust
    seven()
}
