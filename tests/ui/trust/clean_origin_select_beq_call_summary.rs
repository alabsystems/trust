//@ needs-trust-verify
//@ edition: 2021
//@ revisions: beq_eq beq_false_lift crc_poly_mask wrong_arm bitor_havocked
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[beq_eq] check-pass
//@[beq_false_lift] check-pass
//@[crc_poly_mask] check-pass
//@[wrong_arm] check-fail
//@[bitor_havocked] check-fail
//! **A caller of a `==`-lifted select (`SelectBeq` / `SelectBeqGeneral`) island
//! `def` gets its totality and definitional value summary (Trust, 2026-10-20).**
//!
//! * `beq_eq`: `SelectBeq` (`if a == b then a else 0`).
//! * `beq_false_lift`: `SelectBeqGeneral` with `scrutinee = false`
//!   (`if (a == 0) = false then 1 else 0`), preserving polarity without
//!   swapping arms.
//! * `crc_poly_mask`: `SelectBeqGeneral` with a computed `BitAnd` mask operand
//!   (`if (crc &&& 1) == 0 then 0 else 3988292384`, the IEEE 802.3 CRC-32
//!   polynomial selector in `astream-wire`).
//! * `wrong_arm`: a false caller claim (`result == 0`) over `crc32_poly_select`
//!   is refuted.
//! * `bitor_havocked`: `SelectBeqGeneral` with a `BitOr` operand (`|`) is
//!   panic-free (no unregistered-callee error), while its result stays havocked
//!   so a value claim (`result <= 1`) fails closed.

#[cfg(beq_eq)]
clean {
    def eq_or_zero (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else 0
}

#[cfg(beq_eq)]
pub fn call_eq_or_zero(a: u64, b: u64) -> u64
    ensures (a == b && result == a) || (a != b && result == 0)
{
    eq_or_zero(a, b)
}

#[cfg(beq_false_lift)]
clean {
    def nonzero_bit (a : UInt32) : UInt32 := if (a == 0) = false then 1 else 0
}

#[cfg(beq_false_lift)]
pub fn call_nonzero_bit(a: u32) -> u32
    ensures result <= 1 && ((a != 0 && result == 1) || (a == 0 && result == 0))
{
    nonzero_bit(a)
}

#[cfg(any(crc_poly_mask, wrong_arm))]
clean {
    def crc32_poly_select (crc : UInt32) : UInt32 :=
        if (crc &&& 1) == 0 then 0 else 3988292384
}

#[cfg(crc_poly_mask)]
pub fn call_crc32_poly_select(crc: u32) -> u32
    ensures (crc % 2 == 0 && result == 0) || (crc % 2 == 1 && result == 3988292384)
{
    crc32_poly_select(crc)
}

#[cfg(wrong_arm)]
pub fn call_crc32_poly_select(crc: u32) -> u32
    ensures result == 0
{
    //[wrong_arm]~^^^ ERROR Trust
    crc32_poly_select(crc)
}

#[cfg(bitor_havocked)]
clean {
    def bitor_select (x : UInt32) : UInt32 := if (x ||| 1) == 0 then 0 else 1
}

#[cfg(bitor_havocked)]
pub fn call_bitor_select(x: u32) -> u32
    ensures result <= 1
{
    //[bitor_havocked]~^^^ ERROR Trust
    bitor_select(x)
}
