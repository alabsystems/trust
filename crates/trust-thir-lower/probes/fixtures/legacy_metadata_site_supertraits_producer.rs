#![feature(sized_hierarchy)]
pub fn typed<T: core::marker::PointeeSized>() -> u64 { 7 }
pub trait Parent<T, const N: u64> { type Assoc; fn touch(&self); }
pub trait Child<const N: u64>: Parent<u16, N> {}
