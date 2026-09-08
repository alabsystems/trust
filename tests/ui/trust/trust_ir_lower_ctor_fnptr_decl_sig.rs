//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-CTOR (INVALID root 9, full-population frontier — the ledger's LAST
// row): a reified `Constant::FnDef` naming a def with no lowered body (a
// tuple-struct CONSTRUCTOR coerced to a fn pointer) resolved to a
// declaration spelled at the vararg unknown `(...) -> ()`. Unlike a
// direct-call edge — whose drop-lanes lean on that looseness — a fndef
// edge is validator-checked against the TARGET's own functy, so the
// unknown spelling was a guaranteed CallEdgeSignatureMismatch
// (tuple-struct-constructor-pointer: fndef declares (isize) -> (struct)
// while the stub said (...) -> ()). Declarations now carry the OBSERVED
// FULL SIGNATURE when every minting edge was a fndef whose remapped
// `Ty::Func` agreed; any direct-call mint, or a second fndef with a
// different signature, poisons the row back to vararg (decl_id's merge).
// Probe-verified: this module's ctor declarations read functy
// (isize)->(struct) / (isize,isize)->(struct), `main` stays lowered, and
// the module carries 0 validation errors.
#[derive(PartialEq, Debug)]
pub struct Foo(isize);
#[derive(PartialEq, Debug)]
pub struct Bar(isize, isize);

pub fn main() {
    let f: fn(isize) -> Foo = Foo;
    let g: fn(isize, isize) -> Bar = Bar;
    assert_eq!(f(42), Foo(42));
    assert_eq!(g(4, 7), Bar(4, 7));
}
