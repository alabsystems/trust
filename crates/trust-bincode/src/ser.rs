// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The `serde::Serializer`, plus the `SizeChecker` that answers
//! `serialized_size` and enforces the byte limit on the write side.
//!
//! Transcribed from `bincode-1.3.3/src/ser/mod.rs`. Two shapes here are easy
//! to "simplify" wrongly:
//!
//! * `bool`, `Option`'s tag and `u8`/`i8` are RAW single bytes and do **not**
//!   go through the integer encoding, so they are identical under fixint and
//!   varint. Enum variant indices DO go through it (as `u32`).
//! * Fixed arrays and tuples carry NO length prefix; `Vec`/`String`/maps and
//!   `serialize_bytes` DO. `serialize_tuple`/`serialize_struct` therefore write
//!   nothing of their own.

use std::io::Write;

use crate::config::int::{self, IntKind};
use crate::config::{BincodeByteOrder, Endian, IntEncoding, Options, SizeLimit};
use crate::error::{Error, ErrorKind, Result};

/// A serializer that encodes values directly into a `Write`r.
///
/// The configured byte order determines the endianness used for multi-byte
/// values.
pub struct Serializer<W, O: Options> {
    writer: W,
    _options: O,
}

impl<W: Write, O: Options> Serializer<W, O> {
    /// Creates a new `Serializer` with the given `Write`r.
    pub fn new(w: W, options: O) -> Serializer<W, O> {
        Serializer {
            writer: w,
            _options: options,
        }
    }

    #[inline(always)]
    fn endian() -> Endian {
        <O::Endian as BincodeByteOrder>::ENDIAN
    }

    #[inline(always)]
    fn int_kind() -> IntKind {
        <O::IntEncoding as IntEncoding>::KIND
    }

    fn write_all(&mut self, bytes: &[u8]) -> Result<()> {
        self.writer.write_all(bytes).map_err(Into::into)
    }

    pub(crate) fn serialize_byte(&mut self, v: u8) -> Result<()> {
        self.write_all(&[v])
    }

    pub(crate) fn serialize_literal_u16(&mut self, v: u16) -> Result<()> {
        match Self::endian() {
            Endian::Little => self.write_all(&v.to_le_bytes()),
            Endian::Big => self.write_all(&v.to_be_bytes()),
        }
    }

    pub(crate) fn serialize_literal_u32(&mut self, v: u32) -> Result<()> {
        match Self::endian() {
            Endian::Little => self.write_all(&v.to_le_bytes()),
            Endian::Big => self.write_all(&v.to_be_bytes()),
        }
    }

    pub(crate) fn serialize_literal_u64(&mut self, v: u64) -> Result<()> {
        match Self::endian() {
            Endian::Little => self.write_all(&v.to_le_bytes()),
            Endian::Big => self.write_all(&v.to_be_bytes()),
        }
    }

    pub(crate) fn serialize_literal_u128(&mut self, v: u128) -> Result<()> {
        match Self::endian() {
            Endian::Little => self.write_all(&v.to_le_bytes()),
            Endian::Big => self.write_all(&v.to_be_bytes()),
        }
    }
}

impl<'a, W: Write, O: Options> serde::Serializer for &'a mut Serializer<W, O> {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Compound<'a, W, O>;
    type SerializeTuple = Compound<'a, W, O>;
    type SerializeTupleStruct = Compound<'a, W, O>;
    type SerializeTupleVariant = Compound<'a, W, O>;
    type SerializeMap = Compound<'a, W, O>;
    type SerializeStruct = Compound<'a, W, O>;
    type SerializeStructVariant = Compound<'a, W, O>;

    fn serialize_unit(self) -> Result<()> {
        Ok(())
    }

    fn serialize_unit_struct(self, _: &'static str) -> Result<()> {
        Ok(())
    }

    fn serialize_bool(self, v: bool) -> Result<()> {
        self.serialize_byte(v as u8)
    }

    fn serialize_u8(self, v: u8) -> Result<()> {
        self.serialize_byte(v)
    }

    fn serialize_i8(self, v: i8) -> Result<()> {
        self.serialize_byte(v as u8)
    }

    fn serialize_u16(self, v: u16) -> Result<()> {
        int::serialize_u16(self, Serializer::<W, O>::int_kind(), v)
    }

    fn serialize_u32(self, v: u32) -> Result<()> {
        int::serialize_u32(self, Serializer::<W, O>::int_kind(), v)
    }

    fn serialize_u64(self, v: u64) -> Result<()> {
        int::serialize_u64(self, Serializer::<W, O>::int_kind(), v)
    }

    fn serialize_u128(self, v: u128) -> Result<()> {
        int::serialize_u128(self, Serializer::<W, O>::int_kind(), v)
    }

    fn serialize_i16(self, v: i16) -> Result<()> {
        int::serialize_i16(self, Serializer::<W, O>::int_kind(), v)
    }

    fn serialize_i32(self, v: i32) -> Result<()> {
        int::serialize_i32(self, Serializer::<W, O>::int_kind(), v)
    }

    fn serialize_i64(self, v: i64) -> Result<()> {
        int::serialize_i64(self, Serializer::<W, O>::int_kind(), v)
    }

    fn serialize_i128(self, v: i128) -> Result<()> {
        int::serialize_i128(self, Serializer::<W, O>::int_kind(), v)
    }

    fn serialize_f32(self, v: f32) -> Result<()> {
        // Raw IEEE-754 bits in the configured byte order. Never a textual or
        // canonicalised form: NaN payloads and signalling NaNs survive.
        self.serialize_literal_u32(v.to_bits())
    }

    fn serialize_f64(self, v: f64) -> Result<()> {
        self.serialize_literal_u64(v.to_bits())
    }

    fn serialize_str(self, v: &str) -> Result<()> {
        int::serialize_len(self, Serializer::<W, O>::int_kind(), v.len())?;
        self.write_all(v.as_bytes())
    }

    fn serialize_char(self, c: char) -> Result<()> {
        // Raw UTF-8 with NO length prefix; the decoder recovers the width from
        // the first byte.
        let mut buf = [0u8; 4];
        let encoded = c.encode_utf8(&mut buf);
        let len = encoded.len();
        self.write_all(&buf[..len])
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<()> {
        int::serialize_len(self, Serializer::<W, O>::int_kind(), v.len())?;
        self.write_all(v)
    }

    fn serialize_none(self) -> Result<()> {
        self.serialize_byte(0)
    }

    fn serialize_some<T: ?Sized>(self, v: &T) -> Result<()>
    where
        T: serde::Serialize,
    {
        self.serialize_byte(1)?;
        v.serialize(self)
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq> {
        let len = len.ok_or(ErrorKind::SequenceMustHaveLength)?;
        int::serialize_len(self, Serializer::<W, O>::int_kind(), len)?;
        Ok(Compound { ser: self })
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple> {
        Ok(Compound { ser: self })
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        Ok(Compound { ser: self })
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        int::serialize_u32(self, Serializer::<W, O>::int_kind(), variant_index)?;
        Ok(Compound { ser: self })
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap> {
        let len = len.ok_or(ErrorKind::SequenceMustHaveLength)?;
        int::serialize_len(self, Serializer::<W, O>::int_kind(), len)?;
        Ok(Compound { ser: self })
    }

    fn serialize_struct(self, _name: &'static str, _len: usize) -> Result<Self::SerializeStruct> {
        Ok(Compound { ser: self })
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant> {
        int::serialize_u32(self, Serializer::<W, O>::int_kind(), variant_index)?;
        Ok(Compound { ser: self })
    }

    fn serialize_newtype_struct<T: ?Sized>(self, _name: &'static str, value: &T) -> Result<()>
    where
        T: serde::ser::Serialize,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T: ?Sized>(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        value: &T,
    ) -> Result<()>
    where
        T: serde::ser::Serialize,
    {
        int::serialize_u32(self, Serializer::<W, O>::int_kind(), variant_index)?;
        value.serialize(self)
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
    ) -> Result<()> {
        int::serialize_u32(self, Serializer::<W, O>::int_kind(), variant_index)
    }

    // NOTE: `collect_str` is deliberately NOT overridden. serde's default
    // routes it through `serialize_str`, and the incumbent inherits exactly
    // that default; overriding it here would be a divergence risk for no gain.

    fn is_human_readable(&self) -> bool {
        false
    }
}

/// Counts the bytes a value would occupy, and is where the byte limit is
/// actually enforced on the write side.
pub(crate) struct SizeChecker<O: Options> {
    pub options: O,
    pub total: u64,
}

impl<O: Options> SizeChecker<O> {
    fn add_raw(&mut self, size: u64) -> Result<()> {
        self.options.limit().add(size)?;
        self.total += size;
        Ok(())
    }

    fn add_discriminant(&mut self, idx: u32) -> Result<()> {
        let bytes = int::u32_size(SizeChecker::<O>::int_kind(), idx);
        self.add_raw(bytes)
    }

    fn add_len(&mut self, len: usize) -> Result<()> {
        let bytes = int::len_size(SizeChecker::<O>::int_kind(), len);
        self.add_raw(bytes)
    }

    #[inline(always)]
    fn int_kind() -> IntKind {
        <O::IntEncoding as IntEncoding>::KIND
    }
}

impl<'a, O: Options> serde::Serializer for &'a mut SizeChecker<O> {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = SizeCompound<'a, O>;
    type SerializeTuple = SizeCompound<'a, O>;
    type SerializeTupleStruct = SizeCompound<'a, O>;
    type SerializeTupleVariant = SizeCompound<'a, O>;
    type SerializeMap = SizeCompound<'a, O>;
    type SerializeStruct = SizeCompound<'a, O>;
    type SerializeStructVariant = SizeCompound<'a, O>;

    fn serialize_unit(self) -> Result<()> {
        Ok(())
    }

    fn serialize_unit_struct(self, _: &'static str) -> Result<()> {
        Ok(())
    }

    fn serialize_bool(self, _: bool) -> Result<()> {
        self.add_raw(1)
    }

    fn serialize_u8(self, _: u8) -> Result<()> {
        self.add_raw(1)
    }

    fn serialize_i8(self, _: i8) -> Result<()> {
        self.add_raw(1)
    }

    fn serialize_u16(self, v: u16) -> Result<()> {
        self.add_raw(int::u16_size(SizeChecker::<O>::int_kind(), v))
    }

    fn serialize_u32(self, v: u32) -> Result<()> {
        self.add_raw(int::u32_size(SizeChecker::<O>::int_kind(), v))
    }

    fn serialize_u64(self, v: u64) -> Result<()> {
        self.add_raw(int::u64_size(SizeChecker::<O>::int_kind(), v))
    }

    fn serialize_u128(self, v: u128) -> Result<()> {
        self.add_raw(int::u128_size(SizeChecker::<O>::int_kind(), v))
    }

    fn serialize_i16(self, v: i16) -> Result<()> {
        self.add_raw(int::i16_size(SizeChecker::<O>::int_kind(), v))
    }

    fn serialize_i32(self, v: i32) -> Result<()> {
        self.add_raw(int::i32_size(SizeChecker::<O>::int_kind(), v))
    }

    fn serialize_i64(self, v: i64) -> Result<()> {
        self.add_raw(int::i64_size(SizeChecker::<O>::int_kind(), v))
    }

    fn serialize_i128(self, v: i128) -> Result<()> {
        self.add_raw(int::i128_size(SizeChecker::<O>::int_kind(), v))
    }

    fn serialize_f32(self, _: f32) -> Result<()> {
        self.add_raw(4)
    }

    fn serialize_f64(self, _: f64) -> Result<()> {
        self.add_raw(8)
    }

    fn serialize_str(self, v: &str) -> Result<()> {
        self.add_len(v.len())?;
        self.add_raw(v.len() as u64)
    }

    fn serialize_char(self, c: char) -> Result<()> {
        self.add_raw(c.len_utf8() as u64)
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<()> {
        self.add_len(v.len())?;
        self.add_raw(v.len() as u64)
    }

    fn serialize_none(self) -> Result<()> {
        self.add_raw(1)
    }

    fn serialize_some<T: ?Sized>(self, v: &T) -> Result<()>
    where
        T: serde::Serialize,
    {
        self.add_raw(1)?;
        v.serialize(self)
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq> {
        let len = len.ok_or(ErrorKind::SequenceMustHaveLength)?;
        self.add_len(len)?;
        Ok(SizeCompound { ser: self })
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple> {
        Ok(SizeCompound { ser: self })
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        Ok(SizeCompound { ser: self })
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        self.add_raw(int::u32_size(SizeChecker::<O>::int_kind(), variant_index))?;
        Ok(SizeCompound { ser: self })
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap> {
        let len = len.ok_or(ErrorKind::SequenceMustHaveLength)?;
        self.add_len(len)?;
        Ok(SizeCompound { ser: self })
    }

    fn serialize_struct(self, _name: &'static str, _len: usize) -> Result<Self::SerializeStruct> {
        Ok(SizeCompound { ser: self })
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant> {
        self.add_discriminant(variant_index)?;
        Ok(SizeCompound { ser: self })
    }

    fn serialize_newtype_struct<V: serde::Serialize + ?Sized>(
        self,
        _name: &'static str,
        v: &V,
    ) -> Result<()> {
        v.serialize(self)
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
    ) -> Result<()> {
        self.add_discriminant(variant_index)
    }

    fn serialize_newtype_variant<V: serde::Serialize + ?Sized>(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        value: &V,
    ) -> Result<()> {
        self.add_discriminant(variant_index)?;
        value.serialize(self)
    }

    fn is_human_readable(&self) -> bool {
        false
    }
}

/// The compound serializer used for every aggregate kind; none of them write
/// anything of their own beyond what the entry point already wrote.
pub struct Compound<'a, W: 'a, O: Options + 'a> {
    ser: &'a mut Serializer<W, O>,
}

macro_rules! impl_compound {
    ($trait:ident, $method:ident) => {
        impl<'a, W, O> serde::ser::$trait for Compound<'a, W, O>
        where
            W: Write,
            O: Options,
        {
            type Ok = ();
            type Error = Error;

            #[inline]
            fn $method<T: ?Sized>(&mut self, value: &T) -> Result<()>
            where
                T: serde::ser::Serialize,
            {
                value.serialize(&mut *self.ser)
            }

            #[inline]
            fn end(self) -> Result<()> {
                Ok(())
            }
        }
    };
}

impl_compound!(SerializeSeq, serialize_element);
impl_compound!(SerializeTuple, serialize_element);
impl_compound!(SerializeTupleStruct, serialize_field);
impl_compound!(SerializeTupleVariant, serialize_field);

impl<'a, W, O> serde::ser::SerializeMap for Compound<'a, W, O>
where
    W: Write,
    O: Options,
{
    type Ok = ();
    type Error = Error;

    #[inline]
    fn serialize_key<K: ?Sized>(&mut self, value: &K) -> Result<()>
    where
        K: serde::ser::Serialize,
    {
        value.serialize(&mut *self.ser)
    }

    #[inline]
    fn serialize_value<V: ?Sized>(&mut self, value: &V) -> Result<()>
    where
        V: serde::ser::Serialize,
    {
        value.serialize(&mut *self.ser)
    }

    #[inline]
    fn end(self) -> Result<()> {
        Ok(())
    }
}

macro_rules! impl_compound_named {
    ($trait:ident) => {
        impl<'a, W, O> serde::ser::$trait for Compound<'a, W, O>
        where
            W: Write,
            O: Options,
        {
            type Ok = ();
            type Error = Error;

            #[inline]
            fn serialize_field<T: ?Sized>(&mut self, _key: &'static str, value: &T) -> Result<()>
            where
                T: serde::ser::Serialize,
            {
                value.serialize(&mut *self.ser)
            }

            #[inline]
            fn end(self) -> Result<()> {
                Ok(())
            }
        }
    };
}

impl_compound_named!(SerializeStruct);
impl_compound_named!(SerializeStructVariant);

pub(crate) struct SizeCompound<'a, S: Options + 'a> {
    ser: &'a mut SizeChecker<S>,
}

macro_rules! impl_size_compound {
    ($trait:ident, $method:ident) => {
        impl<'a, O: Options> serde::ser::$trait for SizeCompound<'a, O> {
            type Ok = ();
            type Error = Error;

            #[inline]
            fn $method<T: ?Sized>(&mut self, value: &T) -> Result<()>
            where
                T: serde::ser::Serialize,
            {
                value.serialize(&mut *self.ser)
            }

            #[inline]
            fn end(self) -> Result<()> {
                Ok(())
            }
        }
    };
}

impl_size_compound!(SerializeSeq, serialize_element);
impl_size_compound!(SerializeTuple, serialize_element);
impl_size_compound!(SerializeTupleStruct, serialize_field);
impl_size_compound!(SerializeTupleVariant, serialize_field);

impl<'a, O: Options + 'a> serde::ser::SerializeMap for SizeCompound<'a, O> {
    type Ok = ();
    type Error = Error;

    #[inline]
    fn serialize_key<K: ?Sized>(&mut self, value: &K) -> Result<()>
    where
        K: serde::ser::Serialize,
    {
        value.serialize(&mut *self.ser)
    }

    #[inline]
    fn serialize_value<V: ?Sized>(&mut self, value: &V) -> Result<()>
    where
        V: serde::ser::Serialize,
    {
        value.serialize(&mut *self.ser)
    }

    #[inline]
    fn end(self) -> Result<()> {
        Ok(())
    }
}

macro_rules! impl_size_compound_named {
    ($trait:ident) => {
        impl<'a, O: Options> serde::ser::$trait for SizeCompound<'a, O> {
            type Ok = ();
            type Error = Error;

            #[inline]
            fn serialize_field<T: ?Sized>(&mut self, _key: &'static str, value: &T) -> Result<()>
            where
                T: serde::ser::Serialize,
            {
                value.serialize(&mut *self.ser)
            }

            #[inline]
            fn end(self) -> Result<()> {
                Ok(())
            }
        }
    };
}

impl_size_compound_named!(SerializeStruct);
impl_size_compound_named!(SerializeStructVariant);
