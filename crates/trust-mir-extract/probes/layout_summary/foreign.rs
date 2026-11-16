//! Separate-crate declarations whose non-generic root hides an opaque field.
#![feature(type_alias_impl_trait)]
#![allow(dead_code)]
pub type Hidden = impl Copy;
#[define_opaque(Hidden)]
pub fn define_hidden() -> Hidden {
    1u8
}
pub struct ForeignOpaque {
    pub field: Hidden,
}

pub trait PrimitiveStorage: Copy {
    type Out;
}
impl PrimitiveStorage for u8 {
    type Out = [u8; 2];
}
pub trait OpaqueStorage
where
    Hidden: Copy,
{
    type Out;
}
impl OpaqueStorage for u8 {
    type Out = u8;
}
pub struct Nominal(pub u8);
pub trait NominalBound {}
impl NominalBound for Nominal {}
pub trait NominalStorage: NominalBound {
    type Out;
}
impl NominalStorage for Nominal {
    type Out = u8;
}
