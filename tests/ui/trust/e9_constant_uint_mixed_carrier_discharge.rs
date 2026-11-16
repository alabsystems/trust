//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E9-CONSTANT-UINT-MIXED-1 (TG15 residual 2): an unsigned constant behind a
//! parameter at a DIFFERENT carrier. `ConstantUint`'s arity-preserving route was
//! single-domain (`admit_expr_function`), so `fn six(flag: bool) -> u8 { 6 }`
//! minted nothing and every clause naming `six_isl(flag)` was refused. It now
//! mints through the E6 tree producer with each parameter at its own carrier, as
//! the signed `ConstantInt` route already does. The
//! wrong-value twin is `e9_constant_uint_mixed_carrier_undischarged.rs`.

clean {
    def six_isl (flag : Bool) : UInt8 := 6
    def six_of_word (w : UInt32) : UInt64 := 6
}

pub fn six(flag: bool) -> u8
    ensures result == six_isl(flag)
{
    6
}

pub fn six_wide(w: u32) -> u64
    ensures result == six_of_word(w)
{
    6
}

fn main() {
    let _ = six(true);
    let _ = six_wide(7);
}
