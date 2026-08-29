// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Integer encodings. Transcribed from `bincode-1.3.3/src/config/int.rs`.
//!
//! # THE TRAP THIS MODULE EXISTS TO GET RIGHT
//!
//! The free functions and the builder default to DIFFERENT int encodings, and
//! getting it backwards corrupts artifacts silently instead of failing:
//!
//! | entry point                              | int encoding | trailing |
//! |------------------------------------------|--------------|----------|
//! | `serialize` / `deserialize` (free fns)   | **fixint**   | allow    |
//! | `DefaultOptions::new()` alone            | **varint**   | reject   |
//!
//! Both live callers in this tree are fixint, little-endian; they differ only
//! in trailing-byte policy and byte limit. Varint is implemented anyway — and
//! pinned by the golden differential — so `DefaultOptions::new()`'s documented
//! default is honest rather than a silent alias for fixint.
//!
//! # Varint, exactly
//!
//! Encoding an unsigned integer `u` (of any type excepting `u8`):
//!
//! 1. `u <= 250` — a single byte with that value. **The ceiling is 250, not
//!    255.**
//! 2. `251 <= u < 2^16` — literal byte `0xFB`, then a `u16`.
//! 3. `2^16 <= u < 2^32` — literal byte `0xFC`, then a `u32`.
//! 4. `2^32 <= u < 2^64` — literal byte `0xFD`, then a `u64`.
//! 5. `2^64 <= u < 2^128` — literal byte `0xFE`, then a `u128`.
//!
//! `0xFF` is a reserved extension point and always errors on decode. The
//! trailing `u16`/`u32`/`u64`/`u128` go through the configured ENDIANNESS, not
//! unconditionally little-endian.
//!
//! Signed integers are zigzag-converted to unsigned first, so `i128::MIN` and
//! `u128::MAX` encode to the same bytes. `u8`/`i8`, `bool` and the `Option`
//! tag are raw bytes and never touch this module.
//!
//! The decoder is deliberately NOT canonical-form-checking: `fb 01 00` decodes
//! to `1` even though `1` re-encodes to the shorter `01`. That malleability is
//! the incumbent's and is preserved.

use std::io::Write;

use crate::config::Options;
use crate::de::read::BincodeRead;
use crate::error::{ErrorKind, Result};

/// The concrete integer encoding a configuration resolves to.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum IntKind {
    /// Fixed-width, little-/big-endian as configured.
    Fixint,
    /// Variable-width with the 251..255 marker scheme, zigzag for signed.
    Varint,
}

/// A marker type naming one integer encoding.
pub trait IntEncoding {
    /// The encoding this marker names.
    const KIND: IntKind;
}

/// Fixed-size integer encoding.
///
/// * Fixed size integers are encoded directly.
/// * Enum discriminants are encoded as `u32`.
/// * Lengths and `usize` are encoded as `u64`.
#[derive(Copy, Clone)]
pub struct FixintEncoding;

/// Variable-size integer encoding (excepting `[ui]8`). See the module docs.
#[derive(Copy, Clone)]
pub struct VarintEncoding;

impl IntEncoding for FixintEncoding {
    const KIND: IntKind = IntKind::Fixint;
}

impl IntEncoding for VarintEncoding {
    const KIND: IntKind = IntKind::Varint;
}

const SINGLE_BYTE_MAX: u8 = 250;
const U16_BYTE: u8 = 251;
const U32_BYTE: u8 = 252;
const U64_BYTE: u8 = 253;
const U128_BYTE: u8 = 254;

// Transcribed verbatim, including the leading and trailing newlines, which are
// part of the observed message text.
const DESERIALIZE_EXTENSION_POINT_ERR: &str = r#"
Byte 255 is treated as an extension point; it should not be encoding anything.
Do you have a mismatched bincode version or configuration?
"#;

// ---------------------------------------------------------------------------
// zigzag
// ---------------------------------------------------------------------------

#[inline(always)]
fn zigzag_encode(n: i64) -> u64 {
    if n < 0 {
        // `!n` is `-n - 1`, so this is `!n * 2 + 1 = -2n - 1`, which avoids the
        // `i64::MIN` overflow the obvious spelling would hit.
        !(n as u64) * 2 + 1
    } else {
        (n as u64) * 2
    }
}

#[inline(always)]
fn zigzag_decode(n: u64) -> i64 {
    if n % 2 == 0 { (n / 2) as i64 } else { !(n / 2) as i64 }
}

#[inline(always)]
fn zigzag128_encode(n: i128) -> u128 {
    if n < 0 {
        !(n as u128) * 2 + 1
    } else {
        (n as u128) * 2
    }
}

#[inline(always)]
fn zigzag128_decode(n: u128) -> i128 {
    if n % 2 == 0 { (n / 2) as i128 } else { !(n / 2) as i128 }
}

// ---------------------------------------------------------------------------
// sizes
// ---------------------------------------------------------------------------

fn varint_size(n: u64) -> u64 {
    if n <= SINGLE_BYTE_MAX as u64 {
        1
    } else if n <= u16::MAX as u64 {
        1 + 2
    } else if n <= u32::MAX as u64 {
        1 + 4
    } else {
        1 + 8
    }
}

fn varint128_size(n: u128) -> u64 {
    if n <= SINGLE_BYTE_MAX as u128 {
        1
    } else if n <= u16::MAX as u128 {
        1 + 2
    } else if n <= u32::MAX as u128 {
        1 + 4
    } else if n <= u64::MAX as u128 {
        1 + 8
    } else {
        1 + 16
    }
}

pub(crate) fn u16_size(kind: IntKind, n: u16) -> u64 {
    match kind {
        IntKind::Fixint => 2,
        IntKind::Varint => varint_size(n as u64),
    }
}

pub(crate) fn u32_size(kind: IntKind, n: u32) -> u64 {
    match kind {
        IntKind::Fixint => 4,
        IntKind::Varint => varint_size(n as u64),
    }
}

pub(crate) fn u64_size(kind: IntKind, n: u64) -> u64 {
    match kind {
        IntKind::Fixint => 8,
        IntKind::Varint => varint_size(n),
    }
}

pub(crate) fn u128_size(kind: IntKind, n: u128) -> u64 {
    match kind {
        IntKind::Fixint => 16,
        IntKind::Varint => varint128_size(n),
    }
}

pub(crate) fn i16_size(kind: IntKind, n: i16) -> u64 {
    match kind {
        IntKind::Fixint => 2,
        IntKind::Varint => varint_size(zigzag_encode(n as i64)),
    }
}

pub(crate) fn i32_size(kind: IntKind, n: i32) -> u64 {
    match kind {
        IntKind::Fixint => 4,
        IntKind::Varint => varint_size(zigzag_encode(n as i64)),
    }
}

pub(crate) fn i64_size(kind: IntKind, n: i64) -> u64 {
    match kind {
        IntKind::Fixint => 8,
        IntKind::Varint => varint_size(zigzag_encode(n)),
    }
}

pub(crate) fn i128_size(kind: IntKind, n: i128) -> u64 {
    match kind {
        IntKind::Fixint => 16,
        IntKind::Varint => varint128_size(zigzag128_encode(n)),
    }
}

/// Sequence/map/string lengths go through the `u64` lane.
pub(crate) fn len_size(kind: IntKind, len: usize) -> u64 {
    u64_size(kind, len as u64)
}

// ---------------------------------------------------------------------------
// serialize
// ---------------------------------------------------------------------------

type Ser<'a, W, O> = &'a mut crate::ser::Serializer<W, O>;

fn serialize_varint<W: Write, O: Options>(ser: Ser<'_, W, O>, n: u64) -> Result<()> {
    if n <= SINGLE_BYTE_MAX as u64 {
        ser.serialize_byte(n as u8)
    } else if n <= u16::MAX as u64 {
        ser.serialize_byte(U16_BYTE)?;
        ser.serialize_literal_u16(n as u16)
    } else if n <= u32::MAX as u64 {
        ser.serialize_byte(U32_BYTE)?;
        ser.serialize_literal_u32(n as u32)
    } else {
        ser.serialize_byte(U64_BYTE)?;
        ser.serialize_literal_u64(n)
    }
}

fn serialize_varint128<W: Write, O: Options>(ser: Ser<'_, W, O>, n: u128) -> Result<()> {
    if n <= SINGLE_BYTE_MAX as u128 {
        ser.serialize_byte(n as u8)
    } else if n <= u16::MAX as u128 {
        ser.serialize_byte(U16_BYTE)?;
        ser.serialize_literal_u16(n as u16)
    } else if n <= u32::MAX as u128 {
        ser.serialize_byte(U32_BYTE)?;
        ser.serialize_literal_u32(n as u32)
    } else if n <= u64::MAX as u128 {
        ser.serialize_byte(U64_BYTE)?;
        ser.serialize_literal_u64(n as u64)
    } else {
        ser.serialize_byte(U128_BYTE)?;
        ser.serialize_literal_u128(n)
    }
}

pub(crate) fn serialize_u16<W: Write, O: Options>(
    ser: Ser<'_, W, O>,
    kind: IntKind,
    val: u16,
) -> Result<()> {
    match kind {
        IntKind::Fixint => ser.serialize_literal_u16(val),
        IntKind::Varint => serialize_varint(ser, val as u64),
    }
}

pub(crate) fn serialize_u32<W: Write, O: Options>(
    ser: Ser<'_, W, O>,
    kind: IntKind,
    val: u32,
) -> Result<()> {
    match kind {
        IntKind::Fixint => ser.serialize_literal_u32(val),
        IntKind::Varint => serialize_varint(ser, val as u64),
    }
}

pub(crate) fn serialize_u64<W: Write, O: Options>(
    ser: Ser<'_, W, O>,
    kind: IntKind,
    val: u64,
) -> Result<()> {
    match kind {
        IntKind::Fixint => ser.serialize_literal_u64(val),
        IntKind::Varint => serialize_varint(ser, val),
    }
}

pub(crate) fn serialize_u128<W: Write, O: Options>(
    ser: Ser<'_, W, O>,
    kind: IntKind,
    val: u128,
) -> Result<()> {
    match kind {
        IntKind::Fixint => ser.serialize_literal_u128(val),
        IntKind::Varint => serialize_varint128(ser, val),
    }
}

pub(crate) fn serialize_i16<W: Write, O: Options>(
    ser: Ser<'_, W, O>,
    kind: IntKind,
    val: i16,
) -> Result<()> {
    match kind {
        IntKind::Fixint => ser.serialize_literal_u16(val as u16),
        IntKind::Varint => serialize_varint(ser, zigzag_encode(val as i64)),
    }
}

pub(crate) fn serialize_i32<W: Write, O: Options>(
    ser: Ser<'_, W, O>,
    kind: IntKind,
    val: i32,
) -> Result<()> {
    match kind {
        IntKind::Fixint => ser.serialize_literal_u32(val as u32),
        IntKind::Varint => serialize_varint(ser, zigzag_encode(val as i64)),
    }
}

pub(crate) fn serialize_i64<W: Write, O: Options>(
    ser: Ser<'_, W, O>,
    kind: IntKind,
    val: i64,
) -> Result<()> {
    match kind {
        IntKind::Fixint => ser.serialize_literal_u64(val as u64),
        IntKind::Varint => serialize_varint(ser, zigzag_encode(val)),
    }
}

pub(crate) fn serialize_i128<W: Write, O: Options>(
    ser: Ser<'_, W, O>,
    kind: IntKind,
    val: i128,
) -> Result<()> {
    match kind {
        IntKind::Fixint => ser.serialize_literal_u128(val as u128),
        IntKind::Varint => serialize_varint128(ser, zigzag128_encode(val)),
    }
}

/// Serializes a sequence length.
pub(crate) fn serialize_len<W: Write, O: Options>(
    ser: Ser<'_, W, O>,
    kind: IntKind,
    len: usize,
) -> Result<()> {
    serialize_u64(ser, kind, len as u64)
}

// ---------------------------------------------------------------------------
// deserialize
// ---------------------------------------------------------------------------

type De<'a, R, O> = &'a mut crate::de::Deserializer<R, O>;

fn deserialize_varint<'de, R: BincodeRead<'de>, O: Options>(de: De<'_, R, O>) -> Result<u64> {
    match de.deserialize_byte()? {
        byte @ 0..=SINGLE_BYTE_MAX => Ok(byte as u64),
        U16_BYTE => Ok(de.deserialize_literal_u16()? as u64),
        U32_BYTE => Ok(de.deserialize_literal_u32()? as u64),
        U64_BYTE => de.deserialize_literal_u64(),
        U128_BYTE => Err(Box::new(ErrorKind::Custom(
            "Invalid value (u128 range): you may have a version or configuration disagreement?"
                .to_string(),
        ))),
        _ => Err(Box::new(ErrorKind::Custom(
            DESERIALIZE_EXTENSION_POINT_ERR.to_string(),
        ))),
    }
}

fn deserialize_varint128<'de, R: BincodeRead<'de>, O: Options>(de: De<'_, R, O>) -> Result<u128> {
    match de.deserialize_byte()? {
        byte @ 0..=SINGLE_BYTE_MAX => Ok(byte as u128),
        U16_BYTE => Ok(de.deserialize_literal_u16()? as u128),
        U32_BYTE => Ok(de.deserialize_literal_u32()? as u128),
        U64_BYTE => Ok(de.deserialize_literal_u64()? as u128),
        U128_BYTE => de.deserialize_literal_u128(),
        _ => Err(Box::new(ErrorKind::Custom(
            DESERIALIZE_EXTENSION_POINT_ERR.to_string(),
        ))),
    }
}

pub(crate) fn deserialize_u16<'de, R: BincodeRead<'de>, O: Options>(
    de: De<'_, R, O>,
    kind: IntKind,
) -> Result<u16> {
    match kind {
        IntKind::Fixint => de.deserialize_literal_u16(),
        IntKind::Varint => deserialize_varint(de).and_then(cast_u64_to_u16),
    }
}

pub(crate) fn deserialize_u32<'de, R: BincodeRead<'de>, O: Options>(
    de: De<'_, R, O>,
    kind: IntKind,
) -> Result<u32> {
    match kind {
        IntKind::Fixint => de.deserialize_literal_u32(),
        IntKind::Varint => deserialize_varint(de).and_then(cast_u64_to_u32),
    }
}

pub(crate) fn deserialize_u64<'de, R: BincodeRead<'de>, O: Options>(
    de: De<'_, R, O>,
    kind: IntKind,
) -> Result<u64> {
    match kind {
        IntKind::Fixint => de.deserialize_literal_u64(),
        IntKind::Varint => deserialize_varint(de),
    }
}

pub(crate) fn deserialize_u128<'de, R: BincodeRead<'de>, O: Options>(
    de: De<'_, R, O>,
    kind: IntKind,
) -> Result<u128> {
    match kind {
        IntKind::Fixint => de.deserialize_literal_u128(),
        IntKind::Varint => deserialize_varint128(de),
    }
}

pub(crate) fn deserialize_i16<'de, R: BincodeRead<'de>, O: Options>(
    de: De<'_, R, O>,
    kind: IntKind,
) -> Result<i16> {
    match kind {
        IntKind::Fixint => Ok(de.deserialize_literal_u16()? as i16),
        IntKind::Varint => deserialize_varint(de)
            .map(zigzag_decode)
            .and_then(cast_i64_to_i16),
    }
}

pub(crate) fn deserialize_i32<'de, R: BincodeRead<'de>, O: Options>(
    de: De<'_, R, O>,
    kind: IntKind,
) -> Result<i32> {
    match kind {
        IntKind::Fixint => Ok(de.deserialize_literal_u32()? as i32),
        IntKind::Varint => deserialize_varint(de)
            .map(zigzag_decode)
            .and_then(cast_i64_to_i32),
    }
}

pub(crate) fn deserialize_i64<'de, R: BincodeRead<'de>, O: Options>(
    de: De<'_, R, O>,
    kind: IntKind,
) -> Result<i64> {
    match kind {
        IntKind::Fixint => Ok(de.deserialize_literal_u64()? as i64),
        IntKind::Varint => deserialize_varint(de).map(zigzag_decode),
    }
}

pub(crate) fn deserialize_i128<'de, R: BincodeRead<'de>, O: Options>(
    de: De<'_, R, O>,
    kind: IntKind,
) -> Result<i128> {
    match kind {
        IntKind::Fixint => Ok(de.deserialize_literal_u128()? as i128),
        IntKind::Varint => deserialize_varint128(de).map(zigzag128_decode),
    }
}

/// Deserializes a sequence length.
pub(crate) fn deserialize_len<'de, R: BincodeRead<'de>, O: Options>(
    de: De<'_, R, O>,
    kind: IntKind,
) -> Result<usize> {
    deserialize_u64(de, kind).and_then(cast_u64_to_usize)
}

fn cast_u64_to_usize(n: u64) -> Result<usize> {
    if n <= usize::MAX as u64 {
        Ok(n as usize)
    } else {
        Err(Box::new(ErrorKind::Custom(format!(
            "Invalid size {}: sizes must fit in a usize (0 to {})",
            n,
            usize::MAX
        ))))
    }
}

fn cast_u64_to_u32(n: u64) -> Result<u32> {
    if n <= u32::MAX as u64 {
        Ok(n as u32)
    } else {
        Err(Box::new(ErrorKind::Custom(format!(
            "Invalid u32 {n}: you may have a version disagreement?",
        ))))
    }
}

fn cast_u64_to_u16(n: u64) -> Result<u16> {
    if n <= u16::MAX as u64 {
        Ok(n as u16)
    } else {
        Err(Box::new(ErrorKind::Custom(format!(
            "Invalid u16 {n}: you may have a version disagreement?",
        ))))
    }
}

fn cast_i64_to_i32(n: i64) -> Result<i32> {
    if n <= i32::MAX as i64 && n >= i32::MIN as i64 {
        Ok(n as i32)
    } else {
        Err(Box::new(ErrorKind::Custom(format!(
            "Invalid i32 {n}: you may have a version disagreement?",
        ))))
    }
}

fn cast_i64_to_i16(n: i64) -> Result<i16> {
    if n <= i16::MAX as i64 && n >= i16::MIN as i64 {
        Ok(n as i16)
    } else {
        Err(Box::new(ErrorKind::Custom(format!(
            "Invalid i16 {n}: you may have a version disagreement?",
        ))))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zigzag_round_trips_and_edges() {
        assert_eq!(zigzag_encode(0), 0);
        for x in 1..512i64 {
            assert_eq!(zigzag_encode(x), (x as u64) * 2);
            assert_eq!(zigzag_encode(-x), (x as u64) * 2 - 1);
        }
        assert_eq!(zigzag_encode(i64::MAX), u64::MAX - 1);
        assert_eq!(zigzag_encode(i64::MIN), u64::MAX);
        assert_eq!(zigzag_decode(u64::MAX - 1), i64::MAX);
        assert_eq!(zigzag_decode(u64::MAX), i64::MIN);
        for x in (0..512u64).map(|x| x * 2) {
            assert_eq!(zigzag_decode(x), x as i64 / 2);
            assert_eq!(zigzag_decode(x + 1), -(x as i64) / 2 - 1);
        }
    }

    #[test]
    fn zigzag128_edges() {
        assert_eq!(zigzag128_encode(0), 0);
        assert_eq!(zigzag128_encode(i128::MIN), u128::MAX);
        assert_eq!(zigzag128_decode(u128::MAX), i128::MIN);
        // The observed consequence: i128::MIN and u128::MAX are the same bytes.
        assert_eq!(zigzag128_encode(i128::MIN), u128::MAX);
    }

    #[test]
    fn single_byte_ceiling_is_250_not_255() {
        assert_eq!(varint_size(250), 1);
        assert_eq!(varint_size(251), 3);
        assert_eq!(varint_size(65535), 3);
        assert_eq!(varint_size(65536), 5);
        assert_eq!(varint_size(u32::MAX as u64), 5);
        assert_eq!(varint_size(u32::MAX as u64 + 1), 9);
        assert_eq!(varint128_size(u64::MAX as u128), 9);
        assert_eq!(varint128_size(u64::MAX as u128 + 1), 17);
    }
}
