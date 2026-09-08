//! Intent fixture for the NUM-PREDICATE stdlib leaf harvest (P1 #2).
//!
//! Every function below exercises one member of the certified core
//! integer-method leaf family at a concrete width. The harvest certifies the
//! `core` bodies these calls resolve to (see `../results.tsv`), extracted by
//! compiling `library/core` itself — NOT this crate (a probe crate dumps only
//! its own bodies; the core callees stay opaque `Call` terminators).
//!
//! Family (24 fns): the SIGNED sign-methods {is_positive, is_negative, signum}
//! on {i8,i16,i32,i64} and the UNSIGNED bit-methods {is_power_of_two,
//! count_ones, trailing_zeros} on {u8,u16,u32,u64}.
//!
//! Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
#![allow(clippy::all)]

// ---- SIGNED sign predicates: `self > 0` / `self < 0` (FULLY_FAITHFUL) ----
pub fn pos_i8(x: i8) -> bool { x.is_positive() }
pub fn pos_i16(x: i16) -> bool { x.is_positive() }
pub fn pos_i32(x: i32) -> bool { x.is_positive() }
pub fn pos_i64(x: i64) -> bool { x.is_positive() }

pub fn neg_i8(x: i8) -> bool { x.is_negative() }
pub fn neg_i16(x: i16) -> bool { x.is_negative() }
pub fn neg_i32(x: i32) -> bool { x.is_negative() }
pub fn neg_i64(x: i64) -> bool { x.is_negative() }

// ---- SIGNED signum: three_way_compare -> Ordering discriminant -> cast ----
pub fn sgn_i8(x: i8) -> i8 { x.signum() }
pub fn sgn_i16(x: i16) -> i16 { x.signum() }
pub fn sgn_i32(x: i32) -> i32 { x.signum() }
pub fn sgn_i64(x: i64) -> i64 { x.signum() }

// ---- UNSIGNED is_power_of_two: `self.count_ones() == 1` (call-spine) ----
pub fn pow2_u8(x: u8) -> bool { x.is_power_of_two() }
pub fn pow2_u16(x: u16) -> bool { x.is_power_of_two() }
pub fn pow2_u32(x: u32) -> bool { x.is_power_of_two() }
pub fn pow2_u64(x: u64) -> bool { x.is_power_of_two() }

// ---- UNSIGNED count_ones: `intrinsics::ctpop(self)` ----
pub fn ones_u8(x: u8) -> u32 { x.count_ones() }
pub fn ones_u16(x: u16) -> u32 { x.count_ones() }
pub fn ones_u32(x: u32) -> u32 { x.count_ones() }
pub fn ones_u64(x: u64) -> u32 { x.count_ones() }

// ---- UNSIGNED trailing_zeros: `intrinsics::cttz(self)` ----
pub fn tz_u8(x: u8) -> u32 { x.trailing_zeros() }
pub fn tz_u16(x: u16) -> u32 { x.trailing_zeros() }
pub fn tz_u32(x: u32) -> u32 { x.trailing_zeros() }
pub fn tz_u64(x: u64) -> u32 { x.trailing_zeros() }
