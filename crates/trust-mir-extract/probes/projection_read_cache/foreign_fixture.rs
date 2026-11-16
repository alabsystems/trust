//! Real foreign SmallVec metadata, independently of the original Clean source.
#![feature(type_alias_impl_trait)]
#![allow(dead_code)]

extern crate smallvec;
use std::sync::Arc;

pub enum Leaf {
    Zero,
    Next(Arc<Leaf>),
    Name(Arc<str>),
}
pub struct Expr {
    pub kind: Kind,
}
pub enum Kind {
    Values(smallvec::SmallVec<[Leaf; 2]>),
    Apply(Arc<Expr>),
}
pub type Hidden = impl Copy;
#[define_opaque(Hidden)]
pub fn define_hidden() -> Hidden {
    0_u8
}
pub struct UnsafeExpr {
    pub kind: Kind,
    pub unsafe_last: Hidden,
}
pub fn case_foreign_repeat(_: &Leaf, _: &Expr, _: &Arc<Expr>) {}
pub fn case_foreign_unsafe(_: &Leaf, _: &Expr, _: &Arc<UnsafeExpr>) {}
