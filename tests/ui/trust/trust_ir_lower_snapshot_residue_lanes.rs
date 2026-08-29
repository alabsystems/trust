//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-DB/ZU/AR): three snapshot-lane residue classes, one fixture.
//!
//! * wave-DB — the `&&place` double borrow rustc's derive(Debug) emits for
//!   the LAST field of every struct: the inner borrow is a ledger-registered
//!   pointer, the outer snapshots that POINTER VALUE into a `Ty::Ptr` slot
//!   (the scalar snapshot argument, the scalar being an address). The Deref
//!   contract is unchanged: `**x` through the slot still fails closed.
//! * wave-ZU — `&()`: the fieldless-struct zero-field round-trip argument,
//!   applied to the bare unit spelling.
//! * wave-AR — `&[array literal]` and `&"str"` (a `&&str`): the Load side's
//!   `pointee_ok` admitted arrays-in-aggregates and every FatPtrKind since
//!   B4.3; the Store side now matches.

#[derive(Debug, PartialEq)]
struct TwoFields {
    a: u32,
    b: u16,
}

fn unit_ref() -> bool {
    let r = &();
    core::mem::size_of_val(r) == 0
}

fn array_ref_len() -> usize {
    let r = &[1u8, 2, 3, 4];
    r.len()
}

fn main() {
    let t = TwoFields { a: 7, b: 9 };
    // derive(Debug)'s fmt for TwoFields passes `&&self.b` — the double
    // borrow this wave admits — and assert_eq! drives the whole machinery.
    assert_eq!(format!("{t:?}"), "TwoFields { a: 7, b: 9 }");
    assert!(unit_ref());
    assert_eq!(array_ref_len(), 4);
    let s = &"hello";
    assert_eq!(s.len(), 5);
}
