#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_inherit_overflow_checks]
pub fn inherit_regular(x: u32) -> u32 { x }
#[rustc_inherit_overflow_checks]
pub fn inherit_generic<T>(x: u32) -> u32 { x }
pub fn plain_regular(x: u32) -> u32 { x }
pub fn plain_generic<T>(x: u32) -> u32 { x }
