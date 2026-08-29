// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The builder-pattern configuration, transcribed from
//! `bincode-1.3.3/src/config/mod.rs`.
//!
//! # Options struct vs the free functions
//!
//! Due to historical reasons, the default options used by the `serialize()` and
//! `deserialize()` family of free functions are DIFFERENT from the defaults
//! created by `DefaultOptions`:
//!
//! |          | Byte limit | Endianness | Int Encoding | Trailing Behavior |
//! |----------|------------|------------|--------------|-------------------|
//! | struct   | Unlimited  | Little     | **Varint**   | **Reject**        |
//! | function | Unlimited  | Little     | **Fixint**   | **Allow**         |
//!
//! To use the struct with the same settings as the functions:
//!
//! ```
//! use trust_bincode::Options;
//! let my_options = trust_bincode::DefaultOptions::new()
//!     .with_fixint_encoding()
//!     .allow_trailing_bytes();
//! ```
//!
//! # `with_limit` is NOT enforced on the slice decode path
//!
//! This is the incumbent's behaviour and it is preserved DELIBERATELY, because
//! "fixing" it would reject payloads that the incumbent accepts.
//! `internal::deserialize_seed` replaces the caller's limit with `Infinite`
//! before decoding a `&[u8]`. The limit IS enforced
//!
//! * on `serialize` / `serialize_into` (via a `serialized_size` pre-pass), and
//! * on `deserialize_from` (the `io::Read` path).
//!
//! `first-party/trust-ir`'s `clean_expr_codec` relies on this: its
//! `.with_limit(64 MiB)` contributes nothing on decode, and the bound is
//! carried entirely by its own explicit `bytes.len() > max_bytes` pre-check.

use std::io::{Read, Write};
use std::marker::PhantomData;

use crate::de::read::BincodeRead;
use crate::error::Result;

pub use self::endian::{BigEndian, BincodeByteOrder, Endian, LittleEndian, NativeEndian};
pub use self::int::{FixintEncoding, IntEncoding, IntKind, VarintEncoding};
pub use self::limit::{Bounded, Infinite, SizeLimit};
pub use self::trailing::{AllowTrailing, RejectTrailing, TrailingBytes};

pub(crate) mod endian;
pub(crate) mod int;
pub(crate) mod limit;
pub(crate) mod trailing;

/// The default options for serialization/deserialization.
///
/// ### Default Configuration
///
/// | Byte limit | Endianness | Int Encoding | Trailing Behavior |
/// |------------|------------|--------------|-------------------|
/// | Unlimited  | Little     | Varint       | Reject            |
///
/// **This is not the configuration the free functions use.** See the module
/// docs.
#[derive(Copy, Clone)]
pub struct DefaultOptions(Infinite);

impl DefaultOptions {
    /// Get a default configuration object.
    pub fn new() -> DefaultOptions {
        DefaultOptions(Infinite)
    }
}

impl Default for DefaultOptions {
    fn default() -> Self {
        Self::new()
    }
}

/// The four type-level knobs a configuration resolves to.
///
/// This is the supertrait that seals [`Options`]: the builder methods live on
/// `Options`, the resolved answers live here. In the incumbent this trait is
/// crate-private; here it is public so that no `private_bounds` lint fires,
/// which is a strict superset of the incumbent's surface and cannot break a
/// rename.
pub trait InternalOptions {
    /// The byte limit in force.
    type Limit: SizeLimit + 'static;
    /// The byte order multi-byte values are written in.
    type Endian: BincodeByteOrder + 'static;
    /// Fixint or varint.
    type IntEncoding: IntEncoding + 'static;
    /// What to do with bytes left over after a slice decode.
    type Trailing: TrailingBytes + 'static;

    /// The live limit counter. `&mut` because `Bounded` is consumed as bytes
    /// are accounted.
    fn limit(&mut self) -> &mut Self::Limit;
}

impl InternalOptions for DefaultOptions {
    type Limit = Infinite;
    type Endian = LittleEndian;
    type IntEncoding = VarintEncoding;
    type Trailing = RejectTrailing;

    #[inline(always)]
    fn limit(&mut self) -> &mut Infinite {
        &mut self.0
    }
}

impl<'a, O: InternalOptions> InternalOptions for &'a mut O {
    type Limit = O::Limit;
    type Endian = O::Endian;
    type IntEncoding = O::IntEncoding;
    type Trailing = O::Trailing;

    #[inline(always)]
    fn limit(&mut self) -> &mut Self::Limit {
        (**self).limit()
    }
}

/// A configuration builder trait whose options are used while serializing and
/// deserializing.
///
/// ### Byte Limit Details
///
/// The purpose of byte-limiting is to prevent denial-of-service attacks whereby
/// malicious input gets deserialization to crash a process by allocating too
/// much memory or keeping a connection open for too long. Read the module docs
/// before relying on it: the slice path does not enforce it.
pub trait Options: InternalOptions + Sized {
    /// Sets the byte limit to be unlimited. This is the default.
    fn with_no_limit(self) -> WithOtherLimit<Self, Infinite> {
        WithOtherLimit::new(self, Infinite)
    }

    /// Sets the byte limit to `limit`.
    fn with_limit(self, limit: u64) -> WithOtherLimit<Self, Bounded> {
        WithOtherLimit::new(self, Bounded(limit))
    }

    /// Sets the endianness to little-endian. This is the default.
    fn with_little_endian(self) -> WithOtherEndian<Self, LittleEndian> {
        WithOtherEndian::new(self)
    }

    /// Sets the endianness to big-endian.
    fn with_big_endian(self) -> WithOtherEndian<Self, BigEndian> {
        WithOtherEndian::new(self)
    }

    /// Sets the endianness to the machine-native endianness.
    fn with_native_endian(self) -> WithOtherEndian<Self, NativeEndian> {
        WithOtherEndian::new(self)
    }

    /// Sets the integer encoding to varint.
    fn with_varint_encoding(self) -> WithOtherIntEncoding<Self, VarintEncoding> {
        WithOtherIntEncoding::new(self)
    }

    /// Sets the integer encoding to fixed-width.
    fn with_fixint_encoding(self) -> WithOtherIntEncoding<Self, FixintEncoding> {
        WithOtherIntEncoding::new(self)
    }

    /// Sets the deserializer to reject trailing bytes (slice path only).
    fn reject_trailing_bytes(self) -> WithOtherTrailing<Self, RejectTrailing> {
        WithOtherTrailing::new(self)
    }

    /// Sets the deserializer to allow trailing bytes (slice path only).
    fn allow_trailing_bytes(self) -> WithOtherTrailing<Self, AllowTrailing> {
        WithOtherTrailing::new(self)
    }

    /// Serializes a serializable object into a `Vec` of bytes using this
    /// configuration.
    #[inline(always)]
    fn serialize<S: ?Sized + serde::Serialize>(self, t: &S) -> Result<Vec<u8>> {
        crate::internal::serialize(t, self)
    }

    /// Returns the size that an object would be if serialized using this
    /// configuration.
    #[inline(always)]
    fn serialized_size<T: ?Sized + serde::Serialize>(self, t: &T) -> Result<u64> {
        crate::internal::serialized_size(t, self)
    }

    /// Serializes an object directly into a `Writer` using this configuration.
    ///
    /// If the serialization would take more bytes than allowed by the size
    /// limit, an error is returned and *no bytes* will be written.
    #[inline(always)]
    fn serialize_into<W: Write, T: ?Sized + serde::Serialize>(self, w: W, t: &T) -> Result<()> {
        crate::internal::serialize_into(w, t, self)
    }

    /// Deserializes a slice of bytes into an instance of `T` using this
    /// configuration.
    ///
    /// Note that the byte limit is NOT applied on this path — see the module
    /// docs.
    #[inline(always)]
    fn deserialize<'a, T: serde::Deserialize<'a>>(self, bytes: &'a [u8]) -> Result<T> {
        crate::internal::deserialize(bytes, self)
    }

    /// Deserializes a slice of bytes with state `seed` using this configuration.
    #[inline(always)]
    fn deserialize_seed<'a, T: serde::de::DeserializeSeed<'a>>(
        self,
        seed: T,
        bytes: &'a [u8],
    ) -> Result<T::Value> {
        crate::internal::deserialize_seed(seed, bytes, self)
    }

    /// Deserializes in place from a `BincodeRead`er.
    #[doc(hidden)]
    #[inline(always)]
    fn deserialize_in_place<'a, R, T>(self, reader: R, place: &mut T) -> Result<()>
    where
        R: BincodeRead<'a>,
        T: serde::de::Deserialize<'a>,
    {
        crate::internal::deserialize_in_place(reader, self, place)
    }

    /// Deserializes an object directly from a `Read`er using this
    /// configuration.
    ///
    /// If this returns an `Error`, `reader` may be in an invalid state.
    #[inline(always)]
    fn deserialize_from<R: Read, T: serde::de::DeserializeOwned>(self, reader: R) -> Result<T> {
        crate::internal::deserialize_from(reader, self)
    }

    /// Deserializes an object directly from a `Read`er with state `seed`.
    #[inline(always)]
    fn deserialize_from_seed<'a, R: Read, T: serde::de::DeserializeSeed<'a>>(
        self,
        seed: T,
        reader: R,
    ) -> Result<T::Value> {
        crate::internal::deserialize_from_seed(seed, reader, self)
    }

    /// Deserializes an object from a custom `BincodeRead`er.
    #[inline(always)]
    fn deserialize_from_custom<'a, R: BincodeRead<'a>, T: serde::de::DeserializeOwned>(
        self,
        reader: R,
    ) -> Result<T> {
        crate::internal::deserialize_from_custom(reader, self)
    }

    /// Deserializes an object from a custom `BincodeRead`er with state `seed`.
    #[inline(always)]
    fn deserialize_from_custom_seed<'a, R: BincodeRead<'a>, T: serde::de::DeserializeSeed<'a>>(
        self,
        seed: T,
        reader: R,
    ) -> Result<T::Value> {
        crate::internal::deserialize_from_custom_seed(seed, reader, self)
    }
}

impl<T: InternalOptions> Options for T {}

/// A configuration struct with a user-specified byte limit.
#[derive(Clone, Copy)]
pub struct WithOtherLimit<O: Options, L: SizeLimit> {
    _options: O,
    pub(crate) new_limit: L,
}

/// A configuration struct with a user-specified endian order.
#[derive(Clone, Copy)]
pub struct WithOtherEndian<O: Options, E: BincodeByteOrder> {
    options: O,
    _endian: PhantomData<E>,
}

/// A configuration struct with a user-specified integer encoding.
#[derive(Clone, Copy)]
pub struct WithOtherIntEncoding<O: Options, I: IntEncoding> {
    options: O,
    _length: PhantomData<I>,
}

/// A configuration struct with a user-specified trailing-bytes behavior.
#[derive(Clone, Copy)]
pub struct WithOtherTrailing<O: Options, T: TrailingBytes> {
    options: O,
    _trailing: PhantomData<T>,
}

impl<O: Options, L: SizeLimit> WithOtherLimit<O, L> {
    #[inline(always)]
    pub(crate) fn new(options: O, limit: L) -> WithOtherLimit<O, L> {
        WithOtherLimit {
            _options: options,
            new_limit: limit,
        }
    }
}

impl<O: Options, E: BincodeByteOrder> WithOtherEndian<O, E> {
    #[inline(always)]
    pub(crate) fn new(options: O) -> WithOtherEndian<O, E> {
        WithOtherEndian {
            options,
            _endian: PhantomData,
        }
    }
}

impl<O: Options, I: IntEncoding> WithOtherIntEncoding<O, I> {
    #[inline(always)]
    pub(crate) fn new(options: O) -> WithOtherIntEncoding<O, I> {
        WithOtherIntEncoding {
            options,
            _length: PhantomData,
        }
    }
}

impl<O: Options, T: TrailingBytes> WithOtherTrailing<O, T> {
    #[inline(always)]
    pub(crate) fn new(options: O) -> WithOtherTrailing<O, T> {
        WithOtherTrailing {
            options,
            _trailing: PhantomData,
        }
    }
}

impl<O: Options, E: BincodeByteOrder + 'static> InternalOptions for WithOtherEndian<O, E> {
    type Limit = O::Limit;
    type Endian = E;
    type IntEncoding = O::IntEncoding;
    type Trailing = O::Trailing;

    #[inline(always)]
    fn limit(&mut self) -> &mut O::Limit {
        self.options.limit()
    }
}

impl<O: Options, L: SizeLimit + 'static> InternalOptions for WithOtherLimit<O, L> {
    type Limit = L;
    type Endian = O::Endian;
    type IntEncoding = O::IntEncoding;
    type Trailing = O::Trailing;

    fn limit(&mut self) -> &mut L {
        &mut self.new_limit
    }
}

impl<O: Options, I: IntEncoding + 'static> InternalOptions for WithOtherIntEncoding<O, I> {
    type Limit = O::Limit;
    type Endian = O::Endian;
    type IntEncoding = I;
    type Trailing = O::Trailing;

    fn limit(&mut self) -> &mut O::Limit {
        self.options.limit()
    }
}

impl<O: Options, T: TrailingBytes + 'static> InternalOptions for WithOtherTrailing<O, T> {
    type Limit = O::Limit;
    type Endian = O::Endian;
    type IntEncoding = O::IntEncoding;
    type Trailing = T;

    fn limit(&mut self) -> &mut O::Limit {
        self.options.limit()
    }
}
