// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The `serde::Deserializer`. Transcribed from `bincode-1.3.3/src/de/mod.rs`.
//!
//! This format is NOT self-describing, so `deserialize_any` cannot work: it
//! returns `ErrorKind::DeserializeAnyNotSupported`, exactly as the incumbent
//! does. `deserialize_identifier` and `deserialize_ignored_any` are likewise
//! refusals, spelled as `Error::custom` so their text matches.
//!
//! # Limit accounting
//!
//! Every primitive read charges its width to `Options::limit()` BEFORE the
//! bytes are taken, and `read_bytes` charges a string/byte payload before the
//! reader is asked for it. That ordering is what makes
//! `string_len20_vs_limit16_no_payload` fail on the limit rather than on EOF.
//!
//! Two reads deliberately do NOT charge the limit, because the incumbent's do
//! not: `deserialize_char` (it goes straight to `read_exact`) and the
//! `Option` tag beyond the one byte its `u8` read already charges.

use std::io::Read;

use serde::de::Error as DeError;
use serde::de::IntoDeserializer;

use self::read::{BincodeRead, IoReader, SliceReader};
use crate::config::int::{self, IntKind};
use crate::config::{BincodeByteOrder, Endian, IntEncoding, Options, SizeLimit};
use crate::error::{Error, ErrorKind, Result};

/// Specialized ways to read data in.
pub mod read;

/// A deserializer that reads bytes from a `BincodeRead`er.
///
/// The configured byte order determines the endianness used to read multi-byte
/// values.
pub struct Deserializer<R, O: Options> {
    pub(crate) reader: R,
    options: O,
}

impl<IR: Read, O: Options> Deserializer<IoReader<IR>, O> {
    /// Creates a new `Deserializer` with a given `Read`er and options.
    pub fn with_reader(r: IR, options: O) -> Self {
        Deserializer {
            reader: IoReader::new(r),
            options,
        }
    }
}

impl<'de, O: Options> Deserializer<SliceReader<'de>, O> {
    /// Creates a new `Deserializer` that will read from the given slice.
    pub fn from_slice(slice: &'de [u8], options: O) -> Self {
        Deserializer {
            reader: SliceReader::new(slice),
            options,
        }
    }
}

impl<'de, R: BincodeRead<'de>, O: Options> Deserializer<R, O> {
    /// Creates a new `Deserializer` with the given `BincodeRead`er.
    pub fn with_bincode_read(r: R, options: O) -> Deserializer<R, O> {
        Deserializer { reader: r, options }
    }

    #[inline(always)]
    fn endian() -> Endian {
        <O::Endian as BincodeByteOrder>::ENDIAN
    }

    #[inline(always)]
    fn int_kind() -> IntKind {
        <O::IntEncoding as IntEncoding>::KIND
    }

    fn read_array<const N: usize>(&mut self) -> Result<[u8; N]> {
        let mut buf = [0u8; N];
        self.reader.read_exact(&mut buf)?;
        Ok(buf)
    }

    pub(crate) fn deserialize_byte(&mut self) -> Result<u8> {
        self.read_bytes(1)?;
        Ok(self.read_array::<1>()?[0])
    }

    pub(crate) fn deserialize_literal_u16(&mut self) -> Result<u16> {
        self.read_bytes(2)?;
        let b = self.read_array::<2>()?;
        Ok(match Self::endian() {
            Endian::Little => u16::from_le_bytes(b),
            Endian::Big => u16::from_be_bytes(b),
        })
    }

    pub(crate) fn deserialize_literal_u32(&mut self) -> Result<u32> {
        self.read_bytes(4)?;
        let b = self.read_array::<4>()?;
        Ok(match Self::endian() {
            Endian::Little => u32::from_le_bytes(b),
            Endian::Big => u32::from_be_bytes(b),
        })
    }

    pub(crate) fn deserialize_literal_u64(&mut self) -> Result<u64> {
        self.read_bytes(8)?;
        let b = self.read_array::<8>()?;
        Ok(match Self::endian() {
            Endian::Little => u64::from_le_bytes(b),
            Endian::Big => u64::from_be_bytes(b),
        })
    }

    pub(crate) fn deserialize_literal_u128(&mut self) -> Result<u128> {
        self.read_bytes(16)?;
        let b = self.read_array::<16>()?;
        Ok(match Self::endian() {
            Endian::Little => u128::from_le_bytes(b),
            Endian::Big => u128::from_be_bytes(b),
        })
    }

    fn read_bytes(&mut self, count: u64) -> Result<()> {
        self.options.limit().add(count)
    }

    fn read_vec(&mut self) -> Result<Vec<u8>> {
        let len = int::deserialize_len(self, Self::int_kind())?;
        self.read_bytes(len as u64)?;
        self.reader.get_byte_buffer(len)
    }

    fn read_string(&mut self) -> Result<String> {
        let vec = self.read_vec()?;
        String::from_utf8(vec).map_err(|e| Box::new(ErrorKind::InvalidUtf8Encoding(e.utf8_error())))
    }
}

impl<'de, 'a, R, O> serde::Deserializer<'de> for &'a mut Deserializer<R, O>
where
    R: BincodeRead<'de>,
    O: Options,
{
    type Error = Error;

    #[inline]
    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        // Not self-describing. This is a refusal, not a gap.
        Err(Box::new(ErrorKind::DeserializeAnyNotSupported))
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        match self.deserialize_byte()? {
            1 => visitor.visit_bool(true),
            0 => visitor.visit_bool(false),
            value => Err(Box::new(ErrorKind::InvalidBoolEncoding(value))),
        }
    }

    #[inline]
    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_u8(self.deserialize_byte()?)
    }

    #[inline]
    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_i8(self.deserialize_byte()? as i8)
    }

    #[inline]
    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        visitor.visit_u16(int::deserialize_u16(self, kind)?)
    }

    #[inline]
    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        visitor.visit_u32(int::deserialize_u32(self, kind)?)
    }

    #[inline]
    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        visitor.visit_u64(int::deserialize_u64(self, kind)?)
    }

    #[inline]
    fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        visitor.visit_u128(int::deserialize_u128(self, kind)?)
    }

    #[inline]
    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        visitor.visit_i16(int::deserialize_i16(self, kind)?)
    }

    #[inline]
    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        visitor.visit_i32(int::deserialize_i32(self, kind)?)
    }

    #[inline]
    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        visitor.visit_i64(int::deserialize_i64(self, kind)?)
    }

    #[inline]
    fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        visitor.visit_i128(int::deserialize_i128(self, kind)?)
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let bits = self.deserialize_literal_u32()?;
        visitor.visit_f32(f32::from_bits(bits))
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let bits = self.deserialize_literal_u64()?;
        visitor.visit_f64(f64::from_bits(bits))
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let error = || -> Error { Box::new(ErrorKind::InvalidCharEncoding) };

        let mut buf = [0u8; 4];

        // Look at the first byte to see how many bytes must be read. NOTE the
        // asymmetry the incumbent has and this keeps: a failure on the FIRST
        // byte propagates the io error, but a failure on the continuation
        // bytes is reported as InvalidCharEncoding.
        self.reader.read_exact(&mut buf[..1])?;
        let width = utf8_char_width(buf[0]);
        if width == 1 {
            return visitor.visit_char(buf[0] as char);
        }
        if width == 0 {
            return Err(error());
        }

        if self.reader.read_exact(&mut buf[1..width]).is_err() {
            return Err(error());
        }

        let res = std::str::from_utf8(&buf[..width])
            .ok()
            .and_then(|s| s.chars().next())
            .ok_or_else(error)?;
        visitor.visit_char(res)
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        let len = int::deserialize_len(self, kind)?;
        self.read_bytes(len as u64)?;
        self.reader.forward_read_str(len, visitor)
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_string(self.read_string()?)
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        let len = int::deserialize_len(self, kind)?;
        self.read_bytes(len as u64)?;
        self.reader.forward_read_bytes(len, visitor)
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_byte_buf(self.read_vec()?)
    }

    fn deserialize_enum<V>(
        self,
        _enum: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_enum(self)
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_seq(SeqAccess {
            deserializer: self,
            len,
        })
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        // The tag is a RAW byte and does not go through the int encoding.
        let value: u8 = serde::de::Deserialize::deserialize(&mut *self)?;
        match value {
            0 => visitor.visit_none(),
            1 => visitor.visit_some(&mut *self),
            v => Err(Box::new(ErrorKind::InvalidTagEncoding(v as usize))),
        }
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        let len = int::deserialize_len(self, kind)?;
        self.deserialize_tuple(len, visitor)
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let kind = Deserializer::<R, O>::int_kind();
        let len = int::deserialize_len(self, kind)?;
        visitor.visit_map(MapAccess {
            deserializer: self,
            len,
        })
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        self.deserialize_tuple(fields.len(), visitor)
    }

    fn deserialize_identifier<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let message = "Bincode does not support Deserializer::deserialize_identifier";
        Err(Error::custom(message))
    }

    fn deserialize_newtype_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_unit_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        self.deserialize_tuple(len, visitor)
    }

    fn deserialize_ignored_any<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        let message = "Bincode does not support Deserializer::deserialize_ignored_any";
        Err(Error::custom(message))
    }

    fn is_human_readable(&self) -> bool {
        false
    }
}

struct SeqAccess<'a, R, O: Options> {
    deserializer: &'a mut Deserializer<R, O>,
    len: usize,
}

impl<'de, 'a, R: BincodeRead<'de>, O: Options> serde::de::SeqAccess<'de> for SeqAccess<'a, R, O> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: serde::de::DeserializeSeed<'de>,
    {
        if self.len > 0 {
            self.len -= 1;
            let value = serde::de::DeserializeSeed::deserialize(seed, &mut *self.deserializer)?;
            Ok(Some(value))
        } else {
            Ok(None)
        }
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.len)
    }
}

struct MapAccess<'a, R, O: Options> {
    deserializer: &'a mut Deserializer<R, O>,
    len: usize,
}

impl<'de, 'a, R: BincodeRead<'de>, O: Options> serde::de::MapAccess<'de> for MapAccess<'a, R, O> {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: serde::de::DeserializeSeed<'de>,
    {
        if self.len > 0 {
            self.len -= 1;
            let key = serde::de::DeserializeSeed::deserialize(seed, &mut *self.deserializer)?;
            Ok(Some(key))
        } else {
            Ok(None)
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: serde::de::DeserializeSeed<'de>,
    {
        serde::de::DeserializeSeed::deserialize(seed, &mut *self.deserializer)
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.len)
    }
}

impl<'de, 'a, R, O> serde::de::EnumAccess<'de> for &'a mut Deserializer<R, O>
where
    R: BincodeRead<'de>,
    O: Options,
{
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: serde::de::DeserializeSeed<'de>,
    {
        // The index goes through the int encoding as a u32, and is then handed
        // to the derive's own variant visitor via serde's `U32Deserializer`.
        // That routing is what produces the familiar
        // "invalid value: integer `99`, expected variant index 0 <= i < 3" —
        // that message is serde_derive's, not this crate's. Do not "improve" it
        // here.
        let kind = Deserializer::<R, O>::int_kind();
        let idx: u32 = int::deserialize_u32(self, kind)?;
        let val: Result<_> = seed.deserialize(idx.into_deserializer());
        Ok((val?, self))
    }
}

impl<'de, 'a, R, O> serde::de::VariantAccess<'de> for &'a mut Deserializer<R, O>
where
    R: BincodeRead<'de>,
    O: Options,
{
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: serde::de::DeserializeSeed<'de>,
    {
        serde::de::DeserializeSeed::deserialize(seed, self)
    }

    fn tuple_variant<V>(self, len: usize, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        serde::de::Deserializer::deserialize_tuple(self, len, visitor)
    }

    fn struct_variant<V>(self, fields: &'static [&'static str], visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'de>,
    {
        serde::de::Deserializer::deserialize_tuple(self, fields.len(), visitor)
    }
}

/// A copy of `core::str::UTF8_CHAR_WIDTH`. `char` is written with no length
/// prefix, so this table is the only thing that makes it self-delimiting.
static UTF8_CHAR_WIDTH: [u8; 256] = [
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, // 0x1F
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, // 0x3F
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, // 0x5F
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, // 0x7F
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, // 0x9F
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, // 0xBF
    0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, // 0xDF
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, // 0xEF
    4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 0xFF
];

fn utf8_char_width(b: u8) -> usize {
    UTF8_CHAR_WIDTH[b as usize] as usize
}

#[cfg(test)]
mod tests {
    use super::UTF8_CHAR_WIDTH;

    #[test]
    fn utf8_char_width_table_matches_the_utf8_definition() {
        // Independent re-derivation, so a transcription typo in the 256-entry
        // table above cannot pass silently.
        for b in 0u8..=255 {
            let expect = match b {
                0x00..=0x7F => 1,
                0x80..=0xBF => 0,
                0xC0..=0xC1 => 0,
                0xC2..=0xDF => 2,
                0xE0..=0xEF => 3,
                0xF0..=0xF4 => 4,
                _ => 0,
            };
            assert_eq!(
                UTF8_CHAR_WIDTH[b as usize], expect,
                "width table wrong at 0x{b:02x}"
            );
        }
    }
}
