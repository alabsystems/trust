//! Intent fixture for the BIT-METHOD stdlib leaf harvest (P1 — the FREE win).
//!
//! Every function below exercises one member of the certified core integer
//! bit-permutation / bit-count leaf family at a concrete width. The harvest
//! certifies the `core` bodies these calls resolve to (see `../results.tsv`),
//! extracted by compiling `library/core` itself — NOT this crate (a probe crate
//! dumps only its own bodies; the core callees stay opaque `Call` terminators).
//!
//! Family (32 fns): {count_zeros, leading_zeros, swap_bytes, reverse_bits} on
//! the UNSIGNED primaries {u8,u16,u32,u64} (the W-BITINTRIN direct-intrinsic
//! shapes) AND the SIGNED {i8,i16,i32,i64} (the cast-into-unsigned-method
//! wall-characterization panel).
//!
//! Method → intrinsic (unsigned, per library/core/src/num/uint_macros.rs):
//!   count_zeros   = (!self).count_ones()               [ctpop of !self]
//!   leading_zeros = intrinsics::ctlz(self as ActualT)  [ctlz]
//!   swap_bytes    = intrinsics::bswap(self as ActualT) as Self   [bswap]
//!   reverse_bits  = intrinsics::bitreverse(self as ActualT) as Self [bitreverse]
//!
//! Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
#![allow(clippy::all)]

// ---- UNSIGNED count_zeros: `(!self).count_ones()` (ctpop of !self) ----
pub fn cz_u8(x: u8) -> u32 { x.count_zeros() }
pub fn cz_u16(x: u16) -> u32 { x.count_zeros() }
pub fn cz_u32(x: u32) -> u32 { x.count_zeros() }
pub fn cz_u64(x: u64) -> u32 { x.count_zeros() }

// ---- UNSIGNED leading_zeros: `intrinsics::ctlz(self as ActualT)` ----
pub fn lz_u8(x: u8) -> u32 { x.leading_zeros() }
pub fn lz_u16(x: u16) -> u32 { x.leading_zeros() }
pub fn lz_u32(x: u32) -> u32 { x.leading_zeros() }
pub fn lz_u64(x: u64) -> u32 { x.leading_zeros() }

// ---- UNSIGNED swap_bytes: `intrinsics::bswap(self as ActualT) as Self` ----
pub fn sb_u8(x: u8) -> u8 { x.swap_bytes() }
pub fn sb_u16(x: u16) -> u16 { x.swap_bytes() }
pub fn sb_u32(x: u32) -> u32 { x.swap_bytes() }
pub fn sb_u64(x: u64) -> u64 { x.swap_bytes() }

// ---- UNSIGNED reverse_bits: `intrinsics::bitreverse(self as ActualT) as Self` ----
pub fn rb_u8(x: u8) -> u8 { x.reverse_bits() }
pub fn rb_u16(x: u16) -> u16 { x.reverse_bits() }
pub fn rb_u32(x: u32) -> u32 { x.reverse_bits() }
pub fn rb_u64(x: u64) -> u64 { x.reverse_bits() }

// ---- SIGNED count_zeros: `(!self).count_ones()` (ctpop of !self) ----
pub fn cz_i8(x: i8) -> u32 { x.count_zeros() }
pub fn cz_i16(x: i16) -> u32 { x.count_zeros() }
pub fn cz_i32(x: i32) -> u32 { x.count_zeros() }
pub fn cz_i64(x: i64) -> u32 { x.count_zeros() }

// ---- SIGNED leading_zeros: `(self as UnsignedT).leading_zeros()` ----
pub fn lz_i8(x: i8) -> u32 { x.leading_zeros() }
pub fn lz_i16(x: i16) -> u32 { x.leading_zeros() }
pub fn lz_i32(x: i32) -> u32 { x.leading_zeros() }
pub fn lz_i64(x: i64) -> u32 { x.leading_zeros() }

// ---- SIGNED swap_bytes: `(self as UnsignedT).swap_bytes() as Self` ----
pub fn sb_i8(x: i8) -> i8 { x.swap_bytes() }
pub fn sb_i16(x: i16) -> i16 { x.swap_bytes() }
pub fn sb_i32(x: i32) -> i32 { x.swap_bytes() }
pub fn sb_i64(x: i64) -> i64 { x.swap_bytes() }

// ---- SIGNED reverse_bits: `(self as UnsignedT).reverse_bits() as Self` ----
pub fn rb_i8(x: i8) -> i8 { x.reverse_bits() }
pub fn rb_i16(x: i16) -> i16 { x.reverse_bits() }
pub fn rb_i32(x: i32) -> i32 { x.reverse_bits() }
pub fn rb_i64(x: i64) -> i64 { x.reverse_bits() }
