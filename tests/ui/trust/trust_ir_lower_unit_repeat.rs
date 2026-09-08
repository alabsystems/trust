//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-RUE): a repeat whose element is a VALUE-LESS UNIT is ONE
//! `Inst::Const`, because every lane of the mapped `Ty::Tuple([Unit; N])` is
//! already its own final value.
//!
//! `map_ty` spells `[(); N]` as a tuple (the first-class `Ty::Array` gate needs
//! a `seed_constant`-able element and `()` has none), and `lower_expr` on a
//! unit correctly returns `None` WITHOUT pushing a tag — a unit is not a value
//! in this IR. So the aggregate builder was being asked to insert a value that
//! does not exist. wave-UF's shipped vocabulary already answers it:
//! `seed_constant_ty` returns `Some(Aggregate([PhantomData; N]))` for exactly
//! this type, and `shape_matches_ty` admits `(PhantomData, Ty::Unit)`.
//!
//! The operand shape is gated affirmatively (empty tuple literal, NamedConst,
//! ConstBlock) on GROUND TRUTH, never on `map_ty`'s `Ty::Unit`, which is
//! overloaded as the fail-closed placeholder. `effectful_unit_still_lowers` is
//! the fence: a unit-typed CALL has effects that must still be emitted.

pub const U: () = ();

pub fn unit_repeat() -> usize {
    let a = [(); 10];
    a.len()
}

pub fn named_const_unit_repeat() -> usize {
    let a = [U; 4];
    a.len()
}

fn bump(c: &mut u32) {
    *c += 1;
}

/// The fence: a unit-typed CALL element is NOT value-less — its effect must run.
pub fn effectful_unit_still_lowers() -> u32 {
    let mut c = 0u32;
    let _a = [bump(&mut c); 1];
    c
}

fn main() {
    assert_eq!(unit_repeat(), 10);
    assert_eq!(named_const_unit_repeat(), 4);
    assert_eq!(effectful_unit_still_lowers(), 1);
}
