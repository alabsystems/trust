#![no_std]
pub struct Marker;
#[inline] pub fn leaf(x:u64)->u64{x^0x55}
#[inline] pub fn chain(x:u64)->u64{leaf(x)^7}
#[inline] pub fn other(x:u64)->u64{x^0x1234}
#[inline] pub fn typed<T>(x:u64)->u64{x^0x99}
#[inline] pub fn nested(x:u64)->u64{typed::<Marker>(x)}
