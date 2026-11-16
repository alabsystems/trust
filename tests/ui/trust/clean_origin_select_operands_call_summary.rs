//@ needs-trust-verify
//@ edition: 2021
//@ revisions: zero_arm clamp_index wrong_arm
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[zero_arm] check-pass
//@[clamp_index] check-pass
//@[wrong_arm] check-fail
//! **A caller of a numeral-armed select island `def` gets its value (Trust,
//! 2026-09-28).**
//!
//! §6f landing 3's `SelectOperands` is the select whose comparison right-hand
//! side and arms may be numerals: `if a < b then a else 0`,
//! `if a < 10 then a else 9`. Its arm in `clean_origin_call_record_of_record`
//! called its caller summary "genuinely the SAME missing lane" as the
//! parameter-armed selects. That lane landed with
//! `clean_origin_select_call_summary.rs`, and it now covers this shape:
//! `_0 == ite(x_l ⊲ R, T, E)` with numeral `R`, `T` or `E`.
//!
//! * `zero_arm`, `clamp_index`: POSITIVE. `clamp_index` uses the summary for a
//!   SAFETY row, an index into a ten-element table.
//! * `wrong_arm`: `ensures result == a` over `if a < b then a else 0` is false
//!   whenever `a > 0` and `a >= b`, so it must stay refuted.

#[cfg(any(zero_arm, wrong_arm))]
clean {
    def below_or_zero (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else 0
}

#[cfg(zero_arm)]
pub fn call_below(a: u64, b: u64) -> u64
    ensures result <= a && result < b || result == 0
{
    below_or_zero(a, b)
}

#[cfg(clamp_index)]
clean {
    def clamp9 (a : UInt32) : UInt32 := if a < 10 then a else 9
}

#[cfg(clamp_index)]
pub fn digit_name(names: [u8; 10], i: u32) -> u8 {
    names[clamp9(i) as usize]
}

#[cfg(wrong_arm)]
pub fn call_below(a: u64, b: u64) -> u64
    ensures result == a
{
    //[wrong_arm]~^^^ ERROR Trust
    below_or_zero(a, b)
}
