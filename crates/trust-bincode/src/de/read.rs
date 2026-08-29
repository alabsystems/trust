// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Byte sources. Transcribed from `bincode-1.3.3/src/de/read.rs`.
//!
//! # There are THREE different end-of-input messages, and that is deliberate
//!
//! Callers of `trust-clean` and `trust-ir` interpolate the error into a
//! user-visible string, so the exact text is pinned by the golden fixture:
//!
//! | path                                              | `Display`                          |
//! |---------------------------------------------------|------------------------------------|
//! | `SliceReader` via `io::Read` (ints, floats, char)  | `io error: unexpected end of file`  |
//! | `SliceReader::get_byte_slice` (String/Vec/bytes)   | `io error: ` — **empty message**    |
//! | `IoReader` (any `deserialize_from`)                | `io error: failed to fill whole buffer` |
//!
//! The empty one is not a bug to fix: it comes from
//! `io::Error::new(UnexpectedEof, "")`, whose `Display` is the empty string,
//! whereas `io::ErrorKind::UnexpectedEof.into()` renders the kind's own text.
//! Both spellings are preserved exactly.
//!
//! # `IoReader::fill_buffer` is the one deliberate implementation divergence
//!
//! The incumbent does `temp_buffer.resize(length, 0)` and then one
//! `read_exact`. A hostile length prefix (`u64::MAX`) therefore attempts a
//! single enormous allocation and ABORTS the process — the capture agent had
//! to skip the reader lanes of the `vec_u8_len_u64_max` case for exactly this
//! reason, and recorded `reader_lanes_run_for_unlimited_configs: false`.
//!
//! This implementation fills in bounded chunks instead, so a short reader
//! errors after the bytes that actually exist. Every OBSERVABLE result is
//! unchanged: on success the buffer holds exactly `length` bytes, and on a
//! short read the error is still `read_exact`'s own
//! `failed to fill whole buffer`. What changes is that a fuzz-hostile input
//! returns `Err` instead of aborting, which is the "deny panics on malformed
//! input" requirement.

use std::io;

use crate::error::{ErrorKind, Result};

/// An optional `Read` trait for advanced usage.
///
/// The `forward_read_*` methods exist because some byte sources want to pass a
/// long-lived borrow to the visitor (`SliceReader` — this is what makes
/// zero-copy `&'de str` deserialization work) and others only have a transient
/// buffer (`IoReader`).
pub trait BincodeRead<'storage>: io::Read {
    /// Check that the next `length` bytes are a valid string and pass it on to
    /// the visitor.
    fn forward_read_str<V>(&mut self, length: usize, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'storage>;

    /// Transfer ownership of the next `length` bytes to the caller.
    fn get_byte_buffer(&mut self, length: usize) -> Result<Vec<u8>>;

    /// Pass a slice of the next `length` bytes on to the visitor.
    fn forward_read_bytes<V>(&mut self, length: usize, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'storage>;
}

/// A `BincodeRead` implementation for byte slices.
pub struct SliceReader<'storage> {
    slice: &'storage [u8],
}

/// A `BincodeRead` implementation for `io::Read`ers.
pub struct IoReader<R> {
    reader: R,
    temp_buffer: Vec<u8>,
}

impl<'storage> SliceReader<'storage> {
    /// Constructs a slice reader.
    pub(crate) fn new(bytes: &'storage [u8]) -> SliceReader<'storage> {
        SliceReader { slice: bytes }
    }

    #[inline(always)]
    fn get_byte_slice(&mut self, length: usize) -> Result<&'storage [u8]> {
        // The bounds check is what keeps a hostile length prefix from ever
        // reaching an allocation on this path: no `Vec` is sized from
        // attacker-controlled input here.
        if length > self.slice.len() {
            return Err(SliceReader::unexpected_eof());
        }
        let (read_slice, remaining) = self.slice.split_at(length);
        self.slice = remaining;
        Ok(read_slice)
    }

    pub(crate) fn is_finished(&self) -> bool {
        self.slice.is_empty()
    }

    #[inline(always)]
    fn unexpected_eof() -> Box<ErrorKind> {
        // The empty message is load-bearing; see the module docs.
        Box::new(ErrorKind::Io(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "",
        )))
    }
}

impl<R> IoReader<R> {
    /// Constructs an `IoReader`.
    pub(crate) fn new(r: R) -> IoReader<R> {
        IoReader {
            reader: r,
            temp_buffer: vec![],
        }
    }
}

impl<'storage> io::Read for SliceReader<'storage> {
    #[inline(always)]
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        if out.len() > self.slice.len() {
            return Err(io::ErrorKind::UnexpectedEof.into());
        }
        let (read_slice, remaining) = self.slice.split_at(out.len());
        out.copy_from_slice(read_slice);
        self.slice = remaining;
        Ok(out.len())
    }

    #[inline(always)]
    fn read_exact(&mut self, out: &mut [u8]) -> io::Result<()> {
        self.read(out).map(|_| ())
    }
}

impl<R: io::Read> io::Read for IoReader<R> {
    #[inline(always)]
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        self.reader.read(out)
    }

    #[inline(always)]
    fn read_exact(&mut self, out: &mut [u8]) -> io::Result<()> {
        self.reader.read_exact(out)
    }
}

impl<'storage> BincodeRead<'storage> for SliceReader<'storage> {
    #[inline(always)]
    fn forward_read_str<V>(&mut self, length: usize, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'storage>,
    {
        let string = match std::str::from_utf8(self.get_byte_slice(length)?) {
            Ok(s) => s,
            Err(e) => return Err(Box::new(ErrorKind::InvalidUtf8Encoding(e))),
        };
        visitor.visit_borrowed_str(string)
    }

    #[inline(always)]
    fn get_byte_buffer(&mut self, length: usize) -> Result<Vec<u8>> {
        self.get_byte_slice(length).map(|x| x.to_vec())
    }

    #[inline(always)]
    fn forward_read_bytes<V>(&mut self, length: usize, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'storage>,
    {
        visitor.visit_borrowed_bytes(self.get_byte_slice(length)?)
    }
}

/// How much is read per `read_exact` call when filling a buffer of unknown
/// trustworthiness. Only an allocation-shape choice — it changes no bytes and
/// no error text.
const IO_FILL_CHUNK: usize = 64 * 1024;

impl<R> IoReader<R>
where
    R: io::Read,
{
    fn fill_buffer(&mut self, length: usize) -> Result<()> {
        self.temp_buffer.clear();
        let mut remaining = length;
        while remaining > 0 {
            let take = remaining.min(IO_FILL_CHUNK);
            let start = self.temp_buffer.len();
            self.temp_buffer.resize(start + take, 0);
            // `read_exact`'s own error is what produces the observed
            // "failed to fill whole buffer" text.
            if let Err(e) = self.reader.read_exact(&mut self.temp_buffer[start..]) {
                self.temp_buffer.clear();
                return Err(e.into());
            }
            remaining -= take;
        }
        Ok(())
    }
}

impl<'a, R> BincodeRead<'a> for IoReader<R>
where
    R: io::Read,
{
    fn forward_read_str<V>(&mut self, length: usize, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'a>,
    {
        self.fill_buffer(length)?;
        let string = match std::str::from_utf8(&self.temp_buffer[..]) {
            Ok(s) => s,
            Err(e) => return Err(Box::new(ErrorKind::InvalidUtf8Encoding(e))),
        };
        visitor.visit_str(string)
    }

    fn get_byte_buffer(&mut self, length: usize) -> Result<Vec<u8>> {
        self.fill_buffer(length)?;
        Ok(std::mem::take(&mut self.temp_buffer))
    }

    fn forward_read_bytes<V>(&mut self, length: usize, visitor: V) -> Result<V::Value>
    where
        V: serde::de::Visitor<'a>,
    {
        self.fill_buffer(length)?;
        visitor.visit_bytes(&self.temp_buffer[..])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Read as _;

    #[test]
    fn fill_buffer_resizes_down_as_well_as_up() {
        let buffer = vec![0u8; 64];
        let mut reader = IoReader::new(buffer.as_slice());
        reader.fill_buffer(20).unwrap();
        assert_eq!(20, reader.temp_buffer.len());
        reader.fill_buffer(30).unwrap();
        assert_eq!(30, reader.temp_buffer.len());
        reader.fill_buffer(5).unwrap();
        assert_eq!(5, reader.temp_buffer.len());
    }

    #[test]
    fn hostile_length_over_a_short_reader_errors_rather_than_allocating() {
        // This is the case the incumbent aborts on. It must return Err.
        let buffer = vec![0u8; 8];
        let mut reader = IoReader::new(buffer.as_slice());
        let err = reader.fill_buffer(usize::MAX).unwrap_err();
        assert_eq!(err.to_string(), "io error: failed to fill whole buffer");
    }

    #[test]
    fn slice_reader_eof_messages_are_the_two_distinct_ones() {
        let mut r = SliceReader::new(&[1, 2]);
        let mut out = [0u8; 4];
        let io_err = r.read_exact(&mut out).unwrap_err();
        assert_eq!(io_err.to_string(), "unexpected end of file");

        let mut r = SliceReader::new(&[1, 2]);
        let slice_err = r.get_byte_slice(4).unwrap_err();
        assert_eq!(slice_err.to_string(), "io error: ");
    }
}
