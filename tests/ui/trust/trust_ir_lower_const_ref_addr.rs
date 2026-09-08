//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-NCA): a THIN shared-reference const is an ADDRESS — a value-less
//! body-scoped extern immutable global stands for the interned referent
//! (the wave-TL/Batch-C/wave-CP vocabulary), the body goes SYMBOLIC, and the
//! flip is structurally foreclosed — so `run-pass` here executes REAL MIR and
//! the asserted values pin that nothing pretended otherwise.

pub struct A(pub u32);
pub const CA: &A = &A(41);
pub const CN: &u32 = &7;

pub fn read_struct_const_ref() -> u32 {
    let r: &A = CA;
    r.0
}

pub fn read_scalar_const_ref() -> u32 {
    *CN
}

fn main() {
    assert_eq!(read_struct_const_ref(), 41);
    assert_eq!(read_scalar_const_ref(), 7);
}
