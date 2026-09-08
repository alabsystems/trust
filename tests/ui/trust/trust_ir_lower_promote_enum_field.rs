//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-PES): a `&mut`-borrowed local whose type is a registered struct
//! carrying a first-class ENUM component joins the promotion pointee set.
//!
//! `snapshotable_aggregate_pointee` already admits a bare `Ty::Enum` as a WHOLE
//! pointee (`&mut Option<()>` promotes clean today), and the shared-borrow
//! snapshot already admits that same enum as a COMPONENT of a registered
//! struct. Only the promotion side lacked the component admission, so
//! `Ty::Struct[Ty::Enum]` fell out of a set both its neighbours accept.
//!
//! Position is the safety argument: the new arm sits AFTER every opaque and
//! non-pure arm, so it can only see a PURE-value struct those declined, and it
//! then takes the SAME `alloc_promoted` the scalar-struct arm takes.

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum E {
    A,
    B,
}

pub struct S {
    pub e: E,
    pub n: u8,
}

pub fn promote_enum_field() -> u8 {
    let mut s = S { e: E::A, n: 1 };
    let r = &mut s;
    r.n += 2;
    r.e = E::B;
    if s.e == E::B { s.n } else { 0 }
}

fn main() {
    assert_eq!(promote_enum_field(), 3);
}
