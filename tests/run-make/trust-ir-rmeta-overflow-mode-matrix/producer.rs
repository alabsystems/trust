#![feature(rustc_attrs)]
#![allow(internal_features)]

#[inline]
pub fn mix(x: u32) -> u32 { x ^ 0x5a5a_5a5a }

#[inline]
pub fn identity(x: u32) -> u32 { x }

#[inline]
#[rustc_inherit_overflow_checks]
pub fn inherited(x: u32) -> u32 { x }
