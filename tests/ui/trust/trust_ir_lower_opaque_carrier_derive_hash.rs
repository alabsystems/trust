//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ check-pass
#![crate_type = "lib"]
//! callarg-unit: `#[derive(Hash)]` on an OPAQUE-LANE enum hands every by-ref payload
//! binding (`__self_0`, bound under match ergonomics on `&self`) to the SIGNED EXTERN
//! edge `std::hash::Hash::hash(ptr, ptr)` as the unit carrier.
//!
//! `Constant` declines first-class registration: its `L1` payload nests structs
//! deeper than `struct_layout_resolvable(_, 8)` walks (the ay-core original nests
//! `RationalWrapper(Ratio<BigInt { sign, data: BigUint { data: Vec<u64> } }>)`), so
//! the derive's `match self { .. }` takes `lower_enum_match_opaque`.
//!
//! MEASURED 2026-09-22 on trustc 3e7b7b15ba (before the fix), this file warned:
//!   final Trust-IR module validation failed [CallArgTypeMismatch] in
//!   `<Constant as std::hash::Hash>::hash`: CallArgTypeMismatch { block: 1,
//!   callee: "std::hash::Hash::hash", arg_index: 0, expected: "ptr", actual: "()", .. }
//! which is ay-core's `<term::value::Constant as Hash>::hash` (blocks 1..=5, block 4
//! twice for the two-field `BitVec { value, width }` arm).
//!
//! After the fix the derive body is refused at the sink and the crate validates: no
//! spanless WARN (no `dont-require-annotations: WARN` waiver on purpose).

use std::hash::Hash;

#[derive(Hash)]
pub struct L5 {
    v: Vec<u64>,
}
#[derive(Hash)]
pub struct L4 {
    a: L5,
}
#[derive(Hash)]
pub struct L3 {
    a: L4,
}
#[derive(Hash)]
pub struct L2 {
    a: L3,
}
#[derive(Hash)]
pub struct L1 {
    a: L2,
}

#[derive(Hash)]
#[non_exhaustive]
pub enum Constant {
    Bool(bool),
    Int(L1),
    BitVec { value: L1, width: u32 },
    String(String),
}

pub fn h(e: &Constant, st: &mut std::collections::hash_map::DefaultHasher) {
    e.hash(st)
}
