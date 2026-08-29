// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Byte order.
//!
//! The incumbent reaches this through the `byteorder` crate. `byteorder` is a
//! third-party unit and the whole point of this crate is to retire third-party
//! units, so the marker types carry an associated `const` instead and the two
//! multi-byte spellings are `to_le_bytes` / `to_be_bytes` in `ser.rs` and
//! `from_le_bytes` / `from_be_bytes` in `de/mod.rs`. Same bytes, no dependency.

/// The concrete byte order a configuration resolves to.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Endian {
    /// Least-significant byte first.
    Little,
    /// Most-significant byte first.
    Big,
}

/// A marker type naming one byte order.
pub trait BincodeByteOrder {
    /// The order this marker names.
    const ENDIAN: Endian;
}

/// Little-endian byte ordering. This is the default.
#[derive(Copy, Clone)]
pub struct LittleEndian;

/// Big-endian byte ordering.
#[derive(Copy, Clone)]
pub struct BigEndian;

/// The native byte ordering of the current system.
#[derive(Copy, Clone)]
pub struct NativeEndian;

impl BincodeByteOrder for LittleEndian {
    const ENDIAN: Endian = Endian::Little;
}

impl BincodeByteOrder for BigEndian {
    const ENDIAN: Endian = Endian::Big;
}

impl BincodeByteOrder for NativeEndian {
    const ENDIAN: Endian = if cfg!(target_endian = "little") {
        Endian::Little
    } else {
        Endian::Big
    };
}
