// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The entry points every public function funnels through. Transcribed from
//! `bincode-1.3.3/src/internal.rs`.
//!
//! Three orderings here are observable and must not be rearranged:
//!
//! 1. **`serialize` runs `serialized_size` FIRST.** That is what makes a
//!    limit violation fail before a single byte is written, and it is why the
//!    limit is enforced on the write side at all — the `Serializer` itself
//!    never consults it.
//! 2. **`serialize_into` only runs the pre-pass when a limit is set**, then
//!    hands the (already-decremented) options to the serializer, which ignores
//!    them.
//! 3. **`deserialize_seed` REPLACES the caller's limit with `Infinite`.** The
//!    byte limit therefore does nothing on the slice decode path. This is the
//!    incumbent's behaviour, it is live in `first-party/trust-ir`, and
//!    "fixing" it would reject payloads the incumbent accepts. See
//!    `config::mod`'s docs.

use std::io::{Read, Write};
use std::marker::PhantomData;

use crate::config::{Infinite, Options, SizeLimit, TrailingBytes, WithOtherLimit};
use crate::de::read::BincodeRead;
use crate::error::Result;

pub(crate) fn serialize_into<W, T: ?Sized, O>(writer: W, value: &T, mut options: O) -> Result<()>
where
    W: Write,
    T: serde::Serialize,
    O: Options,
{
    if options.limit().limit().is_some() {
        // "compute" the size for the side-effect of returning Err if the bound
        // was reached.
        serialized_size(value, &mut options)?;
    }

    let mut serializer = crate::ser::Serializer::<_, O>::new(writer, options);
    serde::Serialize::serialize(value, &mut serializer)
}

pub(crate) fn serialize<T: ?Sized, O>(value: &T, mut options: O) -> Result<Vec<u8>>
where
    T: serde::Serialize,
    O: Options,
{
    let mut writer = {
        let actual_size = serialized_size(value, &mut options)?;
        Vec::with_capacity(actual_size as usize)
    };

    serialize_into(&mut writer, value, options.with_no_limit())?;
    Ok(writer)
}

pub(crate) fn serialized_size<T: ?Sized, O: Options>(value: &T, options: O) -> Result<u64>
where
    T: serde::Serialize,
{
    let mut size_counter = crate::ser::SizeChecker { options, total: 0 };
    let result = value.serialize(&mut size_counter);
    result.map(|_| size_counter.total)
}

pub(crate) fn deserialize_from<R, T, O>(reader: R, options: O) -> Result<T>
where
    R: Read,
    T: serde::de::DeserializeOwned,
    O: Options,
{
    deserialize_from_seed(PhantomData, reader, options)
}

pub(crate) fn deserialize_from_seed<'a, R, T, O>(seed: T, reader: R, options: O) -> Result<T::Value>
where
    R: Read,
    T: serde::de::DeserializeSeed<'a>,
    O: Options,
{
    let reader = crate::de::read::IoReader::new(reader);
    deserialize_from_custom_seed(seed, reader, options)
}

pub(crate) fn deserialize_from_custom<'a, R, T, O>(reader: R, options: O) -> Result<T>
where
    R: BincodeRead<'a>,
    T: serde::de::DeserializeOwned,
    O: Options,
{
    deserialize_from_custom_seed(PhantomData, reader, options)
}

pub(crate) fn deserialize_from_custom_seed<'a, R, T, O>(
    seed: T,
    reader: R,
    options: O,
) -> Result<T::Value>
where
    R: BincodeRead<'a>,
    T: serde::de::DeserializeSeed<'a>,
    O: Options,
{
    let mut deserializer = crate::de::Deserializer::<_, O>::with_bincode_read(reader, options);
    seed.deserialize(&mut deserializer)
}

pub(crate) fn deserialize_in_place<'a, R, T, O>(reader: R, options: O, place: &mut T) -> Result<()>
where
    R: BincodeRead<'a>,
    T: serde::de::Deserialize<'a>,
    O: Options,
{
    let mut deserializer = crate::de::Deserializer::<_, _>::with_bincode_read(reader, options);
    serde::Deserialize::deserialize_in_place(&mut deserializer, place)
}

pub(crate) fn deserialize<'a, T, O>(bytes: &'a [u8], options: O) -> Result<T>
where
    T: serde::de::Deserialize<'a>,
    O: Options,
{
    deserialize_seed(PhantomData, bytes, options)
}

pub(crate) fn deserialize_seed<'a, T, O>(seed: T, bytes: &'a [u8], options: O) -> Result<T::Value>
where
    T: serde::de::DeserializeSeed<'a>,
    O: Options,
{
    // THE LIMIT IS DROPPED HERE. See the module docs.
    let options_no_limit = WithOtherLimit::new(options, Infinite);

    let reader = crate::de::read::SliceReader::new(bytes);
    let mut deserializer = crate::de::Deserializer::with_bincode_read(reader, options_no_limit);
    let val = seed.deserialize(&mut deserializer)?;

    match O::Trailing::check_end(&deserializer.reader) {
        Ok(_) => Ok(val),
        Err(err) => Err(err),
    }
}
