#![feature(adt_const_params, unsized_const_params, extern_types, sized_hierarchy)]
#![allow(incomplete_features)]
use core::marker::ConstParamTy;
#[derive(ConstParamTy, PartialEq, Eq)]
pub struct Params { pub flag: bool, pub pair: (u8, u16) }
pub struct Envelope<'a, T, const N: u64>(pub &'a T);
pub trait Dyn<const N: u64> { type Assoc; fn visit(&self); }
unsafe extern "C" { pub type Opaque; }
pub fn typed<T: core::marker::PointeeSized>() -> u64 { 7 }
pub fn infer<T>(_: T) -> u64 { 7 }
pub fn const_only<const N: u64>() -> u64 { 7 }
pub fn bool_only<const B: bool>() -> u64 { 7 }
pub fn char_only<const C: char>() -> u64 { 7 }
pub fn aggregate<const P: Params>() -> u64 { 7 }
pub fn array<const A: [u16; 2]>() -> u64 { 7 }
pub fn tuple<const T: (u8, bool)>() -> u64 { 7 }
pub fn text<const S: &'static str>() -> u64 { 7 }
