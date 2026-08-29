// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The Trust-owned `bincode 1.x` wire format.
//!
//! This is a drop-in replacement for the third-party `bincode 1.3.3`, written
//! so that `bincode 1.x` — an UNCONDITIONAL `serde` blocker in the `crates/`
//! shipping closure, because its manifest declares `serde` non-optional and
//! ungated — can leave the graph. It has one dependency: the `serde` trait
//! ABI.
//!
//! ```
//! let target: Option<String> = Some("hello world".to_string());
//! let encoded: Vec<u8> = trust_bincode::serialize(&target).unwrap();
//! let decoded: Option<String> = trust_bincode::deserialize(&encoded[..]).unwrap();
//! assert_eq!(target, decoded);
//! ```
//!
//! # THE DEFAULTS DIFFER BETWEEN THE FUNCTIONS AND THE STRUCT
//!
//! |          | Byte limit | Endianness | Int Encoding | Trailing Behavior |
//! |----------|------------|------------|--------------|-------------------|
//! | struct   | Unlimited  | Little     | **Varint**   | **Reject**        |
//! | function | Unlimited  | Little     | **Fixint**   | **Allow**         |
//!
//! Getting this backwards does not fail — it silently writes different bytes.
//! Both live configurations in this tree are fixint/little-endian; they differ
//! only in trailing-byte policy and byte limit.
//!
//! # Known divergences from the incumbent
//!
//! Everything below is deliberate and measured. The golden differential in
//! `tests/golden_bincode1.rs` checks 501 encode observations and 317 decode
//! observations captured from the real `bincode 1.3.3`, and
//! `tests/differential_vs_incumbent.rs` compares against the live incumbent.
//!
//! This list is what the gates have LOOKED for and found. It is not a proof of
//! completeness, and it must not be read as one: divergence 5 below was present
//! and undocumented while this paragraph claimed there were no others, and it
//! took an adversarial pass over a surface the byte gates do not cover to find
//! it. If you add a surface, add a gate for it before adding a line here.
//!
//! 1. **The deprecated legacy `config()` / `Config` builder is not provided.**
//!    (`bincode-1.3.3/src/config/legacy.rs`.) No caller in this tree uses it.
//!    A rename onto this crate of code that calls `bincode::config()` will
//!    fail to compile — loudly, which is the point.
//! 2. **`IoReader::fill_buffer` fills in bounded chunks** rather than
//!    pre-allocating the whole attacker-supplied length. Same bytes, same
//!    error text; a hostile length prefix returns `Err` instead of aborting
//!    the process on a failed allocation. See `de::read`.
//! 3. **The sealing traits are public.** `InternalOptions`, `IntEncoding`,
//!    `BincodeByteOrder`, `SizeLimit` and `TrailingBytes` are `pub` here and
//!    crate-private in the incumbent. That is a strict superset of the
//!    incumbent's surface and cannot break a rename; it exists so no
//!    `private_bounds` lint fires on `pub trait Options: InternalOptions`.
//! 4. **No recursion limit — inherited, not fixed.** Like the incumbent, a
//!    deeply nested hostile input overflows the stack and ABORTS rather than
//!    returning `Err`; `catch_unwind` cannot intercept it. Adding a depth cap
//!    would reject inputs the incumbent accepts, so it is not done here. A
//!    caller that decodes untrusted bytes must bound depth itself — which is
//!    exactly what `first-party/trust-ir`'s `clean_expr_codec` already does
//!    with `DecodeResourceLimits { max_nodes, max_depth }`.
//! 5. **`std::error::Error::source()` returns `Some` where the incumbent
//!    returns `None`,** for the `ErrorKind::Io` variant: this crate chains to
//!    the underlying `io::Error`, the incumbent does not. Found by an
//!    adversarial differential of the error trait surface, NOT by the byte
//!    gates — no encoded byte and no `Display` string is affected, so nothing
//!    that reads or writes an artifact can observe it. Only code that walks an
//!    error chain can, and no caller in this tree does.
//!
//!    It is recorded rather than removed because chaining is strictly more
//!    informative and cannot corrupt an artifact. It is recorded rather than
//!    left silent because this list previously said "nothing else is known to
//!    differ" while this divergence was already pinned as intended behaviour by
//!    `tests/api_surface.rs` — a claim of completeness that had not been
//!    tested, which is the failure mode this crate exists to avoid.
//!
//! And one thing that is NOT a divergence, because the incumbent does it too
//! and code in this tree depends on it: **`with_limit` does nothing on the
//! slice decode path.** See `config`'s module docs.

pub mod config;
pub mod de;
mod error;
mod internal;
mod ser;

pub use config::{DefaultOptions, Options};
pub use de::Deserializer;
pub use de::read::BincodeRead;
pub use error::{Error, ErrorKind, Result};
pub use ser::Serializer;

/// Get a default configuration object.
///
/// **Warning:** this is not the configuration used by the free functions in
/// this module. See the [`config`] module for details.
///
/// | Byte limit | Endianness | Int Encoding | Trailing Behavior |
/// |------------|------------|--------------|-------------------|
/// | Unlimited  | Little     | Varint       | Reject            |
#[inline(always)]
pub fn options() -> DefaultOptions {
    DefaultOptions::new()
}

/// Serializes an object directly into a `Writer` using the default
/// configuration.
///
/// If the serialization would take more bytes than allowed by the size limit,
/// an error is returned and *no bytes* will be written into the `Writer`.
///
/// **Warning:** the default configuration used by this function is fixint, not
/// the varint `DefaultOptions` uses.
pub fn serialize_into<W, T: ?Sized>(writer: W, value: &T) -> Result<()>
where
    W: std::io::Write,
    T: serde::Serialize,
{
    DefaultOptions::new()
        .with_fixint_encoding()
        .serialize_into(writer, value)
}

/// Serializes a serializable object into a `Vec` of bytes using the default
/// configuration.
///
/// **Warning:** the default configuration used by this function is fixint with
/// trailing bytes allowed, not the varint/reject `DefaultOptions` uses.
pub fn serialize<T: ?Sized>(value: &T) -> Result<Vec<u8>>
where
    T: serde::Serialize,
{
    DefaultOptions::new()
        .with_fixint_encoding()
        .allow_trailing_bytes()
        .serialize(value)
}

/// Deserializes an object directly from a `Read`er using the default
/// configuration.
///
/// If this returns an `Error`, `reader` may be in an invalid state.
pub fn deserialize_from<R, T>(reader: R) -> Result<T>
where
    R: std::io::Read,
    T: serde::de::DeserializeOwned,
{
    DefaultOptions::new()
        .with_fixint_encoding()
        .allow_trailing_bytes()
        .deserialize_from(reader)
}

/// Deserializes an object from a custom `BincodeRead`er using the default
/// configuration.
///
/// If this returns an `Error`, `reader` may be in an invalid state.
pub fn deserialize_from_custom<'a, R, T>(reader: R) -> Result<T>
where
    R: de::read::BincodeRead<'a>,
    T: serde::de::DeserializeOwned,
{
    DefaultOptions::new()
        .with_fixint_encoding()
        .allow_trailing_bytes()
        .deserialize_from_custom(reader)
}

/// Only use this if you know what you're doing.
#[doc(hidden)]
pub fn deserialize_in_place<'a, R, T>(reader: R, place: &mut T) -> Result<()>
where
    T: serde::de::Deserialize<'a>,
    R: BincodeRead<'a>,
{
    DefaultOptions::new()
        .with_fixint_encoding()
        .allow_trailing_bytes()
        .deserialize_in_place(reader, place)
}

/// Deserializes a slice of bytes into an instance of `T` using the default
/// configuration.
///
/// **Warning:** the default configuration used by this function is fixint with
/// trailing bytes ALLOWED — a slice with junk after a complete value is
/// accepted here and rejected by `DefaultOptions::new()`.
pub fn deserialize<'a, T>(bytes: &'a [u8]) -> Result<T>
where
    T: serde::de::Deserialize<'a>,
{
    DefaultOptions::new()
        .with_fixint_encoding()
        .allow_trailing_bytes()
        .deserialize(bytes)
}

/// Returns the size that an object would be if serialized using the default
/// configuration.
pub fn serialized_size<T: ?Sized>(value: &T) -> Result<u64>
where
    T: serde::Serialize,
{
    DefaultOptions::new()
        .with_fixint_encoding()
        .allow_trailing_bytes()
        .serialized_size(value)
}
