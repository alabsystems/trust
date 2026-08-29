// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The error type, byte-for-byte compatible with `bincode 1.3.3`'s.
//!
//! Two things here are load-bearing and must not be "cleaned up":
//!
//! 1. **`Error` is `Box<ErrorKind>`, not a struct.** Callers write
//!    `Result<T, bincode::Error>` and some match on `*err`. Changing the
//!    shape breaks a rename even though every message still matches.
//! 2. **The `Display` text is API.** `crates/trust-clean/src/clean_bridge.rs`
//!    and `first-party/trust-ir/.../clean_expr_codec.rs` both interpolate the
//!    error into a user-visible string (`format!("decode Clean Expr v1: {error}")`).
//!    Every string below is transcribed from `bincode-1.3.3/src/error.rs` and
//!    is pinned by `tests/golden_bincode1.rs` against messages captured from
//!    the real incumbent.
//!
//! The `Debug` rendering is pinned too — the fixture records `error_debug` for
//! every decode observation, so the derived `Debug` and the exact
//! `std::io::Error` construction (`Error::new(UnexpectedEof, "")` vs
//! `ErrorKind::UnexpectedEof.into()` vs a real `read_exact` failure) all have
//! to line up. See `de::read` for why there are three different EOF messages.

use std::error::Error as StdError;
use std::fmt;
use std::io;
use std::str::Utf8Error;

/// The result of a serialization or deserialization operation.
pub type Result<T> = std::result::Result<T, Error>;

/// An error that can be produced during (de)serializing.
pub type Error = Box<ErrorKind>;

/// The kind of error that can be produced during a serialization or
/// deserialization.
#[derive(Debug)]
pub enum ErrorKind {
    /// If the error stems from the reader/writer that is being used
    /// during (de)serialization, that error will be stored and returned here.
    Io(io::Error),
    /// Returned if the deserializer attempts to deserialize a string that is
    /// not valid utf8.
    InvalidUtf8Encoding(Utf8Error),
    /// Returned if the deserializer attempts to deserialize a bool that was
    /// not encoded as either a 1 or a 0.
    InvalidBoolEncoding(u8),
    /// Returned if the deserializer attempts to deserialize a char that is not
    /// in the correct format.
    InvalidCharEncoding,
    /// Returned if the deserializer attempts to deserialize the tag of an enum
    /// that is not in the expected ranges.
    InvalidTagEncoding(usize),
    /// Serde has a `deserialize_any` method that lets the format hint to the
    /// object which route to take in deserializing. This format is not
    /// self-describing, so it cannot answer.
    DeserializeAnyNotSupported,
    /// If (de)serializing a message takes more than the provided size limit,
    /// this error is returned.
    SizeLimit,
    /// This format can not encode sequences of unknown length (like iterators).
    SequenceMustHaveLength,
    /// A custom error message from Serde.
    Custom(String),
}

impl ErrorKind {
    /// The stable prefix of each message.
    ///
    /// This mirrors the incumbent's (deprecated) `StdError::description`, which
    /// its `Display` impl called. It is a private helper here so that no
    /// deprecated trait method is implemented, while the resulting text is
    /// unchanged. The `Io` arm is unreachable from `Display` — that arm
    /// formats the inner `io::Error` directly, exactly as the incumbent does —
    /// so it does not need to call `io::Error`'s own deprecated
    /// `description()`.
    fn description(&self) -> &str {
        match *self {
            ErrorKind::Io(_) => "io error",
            ErrorKind::InvalidUtf8Encoding(_) => "string is not valid utf8",
            ErrorKind::InvalidBoolEncoding(_) => "invalid u8 while decoding bool",
            ErrorKind::InvalidCharEncoding => "char is not valid",
            ErrorKind::InvalidTagEncoding(_) => "tag for enum is not valid",
            ErrorKind::SequenceMustHaveLength => {
                "Bincode can only encode sequences and maps that have a knowable size ahead of time"
            }
            ErrorKind::DeserializeAnyNotSupported => {
                "Bincode doesn't support serde::Deserializer::deserialize_any"
            }
            ErrorKind::SizeLimit => "the size limit has been reached",
            ErrorKind::Custom(ref msg) => msg,
        }
    }
}

impl StdError for ErrorKind {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match *self {
            ErrorKind::Io(ref err) => Some(err),
            _ => None,
        }
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Box::new(ErrorKind::Io(err))
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            ErrorKind::Io(ref ioerr) => write!(fmt, "io error: {ioerr}"),
            ErrorKind::InvalidUtf8Encoding(ref e) => write!(fmt, "{}: {}", self.description(), e),
            ErrorKind::InvalidBoolEncoding(b) => {
                write!(fmt, "{}, expected 0 or 1, found {}", self.description(), b)
            }
            ErrorKind::InvalidCharEncoding => write!(fmt, "{}", self.description()),
            ErrorKind::InvalidTagEncoding(tag) => {
                write!(fmt, "{}, found {}", self.description(), tag)
            }
            ErrorKind::SequenceMustHaveLength => write!(fmt, "{}", self.description()),
            ErrorKind::SizeLimit => write!(fmt, "{}", self.description()),
            ErrorKind::DeserializeAnyNotSupported => write!(
                fmt,
                "Bincode does not support the serde::Deserializer::deserialize_any method"
            ),
            ErrorKind::Custom(ref s) => s.fmt(fmt),
        }
    }
}

impl serde::de::Error for Error {
    fn custom<T: fmt::Display>(desc: T) -> Error {
        Box::new(ErrorKind::Custom(desc.to_string()))
    }
}

impl serde::ser::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        Box::new(ErrorKind::Custom(msg.to_string()))
    }
}
