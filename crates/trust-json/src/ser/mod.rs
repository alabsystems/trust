// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! JSON serialization, byte-identical to the incumbent.
//!
//! # The seam
//!
//! [`Formatter`] is a deliberate transcription of `serde_json::ser::Formatter`:
//! same method names, same signatures over [`std::io::Write`], same defaults.
//! That is the coordination point with the serde-traits layer — a `Serializer`
//! written against `trust-serde` drives this trait exactly as `serde_json`'s
//! does, so no byte decision has to be re-litigated there. Every choice about
//! *what bytes come out* lives in this file and in [`super::ser::float`].
//!
//! # The escape table is not a style choice
//!
//! Measured against the incumbent (`serde_json` 1.0.151, `src/ser.rs`
//! `static ESCAPE`), transcribed here and re-checked byte-for-byte in
//! `tests/differential_json.rs`:
//!
//! * `"` and `\` are escaped; **`/` is NOT** (a JSON writer is permitted to
//!   escape it, and several do).
//! * `0x08 0x09 0x0A 0x0C 0x0D` use the short forms `\b \t \n \f \r`.
//! * Every other byte below `0x20` becomes `\u00xx` with **lowercase** hex.
//! * **DEL (`0x7F`) is NOT escaped**, and neither is any non-ASCII: UTF-8
//!   bytes pass through unchanged, including U+2028/U+2029, which a
//!   JavaScript-safe writer would escape.

pub mod float;
pub mod int;

use crate::error::{Error, Result};
use crate::map::Map;
use crate::number::N;
use crate::value::Value;
use std::io;

use float::FloatBuffer;
use int::IntBuffer;

/// Represents a character escape code in a type-safe manner.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CharEscape {
    /// An escaped quote `"`.
    Quote,
    /// An escaped reverse solidus `\`.
    ReverseSolidus,
    /// An escaped solidus `/`.
    Solidus,
    /// An escaped backspace character (usually escaped as `\b`).
    Backspace,
    /// An escaped form feed character (usually escaped as `\f`).
    FormFeed,
    /// An escaped line feed character (usually escaped as `\n`).
    LineFeed,
    /// An escaped carriage return character (usually escaped as `\r`).
    CarriageReturn,
    /// An escaped tab character (usually escaped as `\t`).
    Tab,
    /// An escaped ASCII plane control character (usually escaped as
    /// `\u00XX` where `XX` are two hex characters).
    AsciiControl(u8),
}

/// This trait abstracts away serializing the JSON control characters, which
/// allows the user to optionally pretty print the JSON output.
///
/// The method set is a transcription of the incumbent's; see the module docs.
pub trait Formatter {
    #[inline]
    fn write_null<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"null")
    }

    #[inline]
    fn write_bool<W>(&mut self, writer: &mut W, value: bool) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let s = if value {
            b"true".as_slice()
        } else {
            b"false".as_slice()
        };
        writer.write_all(s)
    }

    #[inline]
    fn write_i64<W>(&mut self, writer: &mut W, value: i64) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let mut buffer = IntBuffer::new();
        writer.write_all(buffer.format_i64(value).as_bytes())
    }

    #[inline]
    fn write_i128<W>(&mut self, writer: &mut W, value: i128) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let mut buffer = IntBuffer::new();
        writer.write_all(buffer.format_i128(value).as_bytes())
    }

    #[inline]
    fn write_u64<W>(&mut self, writer: &mut W, value: u64) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let mut buffer = IntBuffer::new();
        writer.write_all(buffer.format_u64(value).as_bytes())
    }

    #[inline]
    fn write_u128<W>(&mut self, writer: &mut W, value: u128) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let mut buffer = IntBuffer::new();
        writer.write_all(buffer.format_u128(value).as_bytes())
    }

    /// Writes a finite `f32`. Non-finite input is the caller's error — the
    /// serializer maps NaN and the infinities to `null` before calling.
    #[inline]
    fn write_f32<W>(&mut self, writer: &mut W, value: f32) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let mut buffer = FloatBuffer::new();
        writer.write_all(buffer.format_finite_f32(value).as_bytes())
    }

    /// Writes a finite `f64`. See [`Formatter::write_f32`].
    #[inline]
    fn write_f64<W>(&mut self, writer: &mut W, value: f64) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let mut buffer = FloatBuffer::new();
        writer.write_all(buffer.format_finite_f64(value).as_bytes())
    }

    /// Writes a number that has already been rendered to a string.
    #[inline]
    fn write_number_str<W>(&mut self, writer: &mut W, value: &str) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(value.as_bytes())
    }

    #[inline]
    fn begin_string<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"\"")
    }

    #[inline]
    fn end_string<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"\"")
    }

    #[inline]
    fn write_string_fragment<W>(&mut self, writer: &mut W, fragment: &str) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(fragment.as_bytes())
    }

    #[inline]
    fn write_char_escape<W>(&mut self, writer: &mut W, char_escape: CharEscape) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        use CharEscape::*;
        let escape_char = match char_escape {
            Quote => b'"',
            ReverseSolidus => b'\\',
            Solidus => b'/',
            Backspace => b'b',
            FormFeed => b'f',
            LineFeed => b'n',
            CarriageReturn => b'r',
            Tab => b't',
            AsciiControl(_) => b'u',
        };
        match char_escape {
            AsciiControl(byte) => {
                // Lowercase, and always four hex digits. Measured.
                static HEX_DIGITS: [u8; 16] = *b"0123456789abcdef";
                let bytes = &[
                    b'\\',
                    escape_char,
                    b'0',
                    b'0',
                    HEX_DIGITS[(byte >> 4) as usize],
                    HEX_DIGITS[(byte & 0xF) as usize],
                ];
                writer.write_all(bytes)
            }
            _ => writer.write_all(&[b'\\', escape_char]),
        }
    }

    #[inline]
    fn begin_array<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"[")
    }

    #[inline]
    fn end_array<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"]")
    }

    #[inline]
    fn begin_array_value<W>(&mut self, writer: &mut W, first: bool) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        if first {
            Ok(())
        } else {
            writer.write_all(b",")
        }
    }

    #[inline]
    fn end_array_value<W>(&mut self, _writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        Ok(())
    }

    #[inline]
    fn begin_object<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"{")
    }

    #[inline]
    fn end_object<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b"}")
    }

    #[inline]
    fn begin_object_key<W>(&mut self, writer: &mut W, first: bool) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        if first {
            Ok(())
        } else {
            writer.write_all(b",")
        }
    }

    #[inline]
    fn end_object_key<W>(&mut self, _writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        Ok(())
    }

    #[inline]
    fn begin_object_value<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b":")
    }

    #[inline]
    fn end_object_value<W>(&mut self, _writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        Ok(())
    }
}

/// The compact JSON formatter: no whitespace anywhere.
#[derive(Clone, Debug, Default)]
pub struct CompactFormatter;

impl Formatter for CompactFormatter {}

/// The pretty JSON formatter.
///
/// The exact shape, measured against the incumbent and pinned in
/// `tests/differential_json.rs`:
///
/// * indent is **two spaces**;
/// * the key/value separator is `": "` (colon SPACE), while the compact
///   formatter writes a bare `":"`;
/// * an EMPTY array or object stays on one line as `[]` / `{}` — the closing
///   bracket only gets a newline when at least one value was written;
/// * there is no trailing newline at the end of the document.
#[derive(Clone, Debug)]
pub struct PrettyFormatter<'a> {
    current_indent: usize,
    has_value: bool,
    indent: &'a [u8],
}

impl<'a> PrettyFormatter<'a> {
    #[must_use]
    pub fn new() -> Self {
        PrettyFormatter::with_indent(b"  ")
    }

    #[must_use]
    pub fn with_indent(indent: &'a [u8]) -> Self {
        PrettyFormatter {
            current_indent: 0,
            has_value: false,
            indent,
        }
    }
}

impl Default for PrettyFormatter<'_> {
    fn default() -> Self {
        PrettyFormatter::new()
    }
}

fn indent<W>(wr: &mut W, n: usize, s: &[u8]) -> io::Result<()>
where
    W: ?Sized + io::Write,
{
    for _ in 0..n {
        wr.write_all(s)?;
    }
    Ok(())
}

impl Formatter for PrettyFormatter<'_> {
    #[inline]
    fn begin_array<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.current_indent += 1;
        self.has_value = false;
        writer.write_all(b"[")
    }

    #[inline]
    fn end_array<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.current_indent -= 1;
        if self.has_value {
            writer.write_all(b"\n")?;
            indent(writer, self.current_indent, self.indent)?;
        }
        writer.write_all(b"]")
    }

    #[inline]
    fn begin_array_value<W>(&mut self, writer: &mut W, first: bool) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(if first { b"\n" } else { b",\n" })?;
        indent(writer, self.current_indent, self.indent)
    }

    #[inline]
    fn end_array_value<W>(&mut self, _writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.has_value = true;
        Ok(())
    }

    #[inline]
    fn begin_object<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.current_indent += 1;
        self.has_value = false;
        writer.write_all(b"{")
    }

    #[inline]
    fn end_object<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.current_indent -= 1;
        if self.has_value {
            writer.write_all(b"\n")?;
            indent(writer, self.current_indent, self.indent)?;
        }
        writer.write_all(b"}")
    }

    #[inline]
    fn begin_object_key<W>(&mut self, writer: &mut W, first: bool) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(if first { b"\n" } else { b",\n" })?;
        indent(writer, self.current_indent, self.indent)
    }

    #[inline]
    fn begin_object_value<W>(&mut self, writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        writer.write_all(b": ")
    }

    #[inline]
    fn end_object_value<W>(&mut self, _writer: &mut W) -> io::Result<()>
    where
        W: ?Sized + io::Write,
    {
        self.has_value = true;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// The escape table, transcribed from the incumbent. Read the module docs
// before changing a single cell: `/` and DEL are deliberately absent.
// ---------------------------------------------------------------------------

const BB: u8 = b'b'; // \x08
const TT: u8 = b't'; // \x09
const NN: u8 = b'n'; // \x0A
const FF: u8 = b'f'; // \x0C
const RR: u8 = b'r'; // \x0D
const QU: u8 = b'"'; // \x22
const BS: u8 = b'\\'; // \x5C
const UU: u8 = b'u'; // \x00...\x1F except the ones above
const __: u8 = 0;

#[rustfmt::skip]
static ESCAPE: [u8; 256] = [
    //  1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
    UU, UU, UU, UU, UU, UU, UU, UU, BB, TT, NN, UU, FF, RR, UU, UU, // 0
    UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, UU, // 1
    __, __, QU, __, __, __, __, __, __, __, __, __, __, __, __, __, // 2
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 3
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 4
    __, __, __, __, __, __, __, __, __, __, __, __, BS, __, __, __, // 5
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 6
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 7
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 8
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 9
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // A
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // B
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // C
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // D
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // E
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // F
];

/// Writes `value` as a JSON string, escaping exactly what the incumbent
/// escapes.
pub fn format_escaped_str<W, F>(writer: &mut W, formatter: &mut F, value: &str) -> io::Result<()>
where
    W: ?Sized + io::Write,
    F: ?Sized + Formatter,
{
    formatter.begin_string(writer)?;
    format_escaped_str_contents(writer, formatter, value)?;
    formatter.end_string(writer)
}

fn format_escaped_str_contents<W, F>(
    writer: &mut W,
    formatter: &mut F,
    value: &str,
) -> io::Result<()>
where
    W: ?Sized + io::Write,
    F: ?Sized + Formatter,
{
    let bytes = value.as_bytes();
    let mut start = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        let escape = ESCAPE[byte as usize];
        if escape == 0 {
            continue;
        }
        if start < i {
            // Only ASCII bytes are ever escaped, so this split is on a char
            // boundary and the slice is valid UTF-8.
            formatter.write_string_fragment(writer, &value[start..i])?;
        }
        let char_escape = match escape {
            BB => CharEscape::Backspace,
            TT => CharEscape::Tab,
            NN => CharEscape::LineFeed,
            FF => CharEscape::FormFeed,
            RR => CharEscape::CarriageReturn,
            QU => CharEscape::Quote,
            BS => CharEscape::ReverseSolidus,
            _ => CharEscape::AsciiControl(byte),
        };
        formatter.write_char_escape(writer, char_escape)?;
        start = i + 1;
    }
    if start < bytes.len() {
        formatter.write_string_fragment(writer, &value[start..])?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Value -> bytes
// ---------------------------------------------------------------------------

fn write_value<W, F>(writer: &mut W, formatter: &mut F, value: &Value) -> io::Result<()>
where
    W: ?Sized + io::Write,
    F: ?Sized + Formatter,
{
    match value {
        Value::Null => formatter.write_null(writer),
        Value::Bool(b) => formatter.write_bool(writer, *b),
        Value::Number(n) => match n.n {
            N::PosInt(u) => formatter.write_u64(writer, u),
            N::NegInt(i) => formatter.write_i64(writer, i),
            // A `Number` cannot hold a non-finite float — `Number::from_f64`
            // rejects them — so this branch is always the finite one. The
            // `null` fallback exists because a serializer reaching a raw
            // non-finite `f64` writes `null`, and keeping the two paths
            // spelled the same way is what makes them stay in agreement.
            N::Float(f) => {
                if f.is_finite() {
                    formatter.write_f64(writer, f)
                } else {
                    formatter.write_null(writer)
                }
            }
        },
        Value::String(s) => format_escaped_str(writer, formatter, s),
        Value::Array(a) => {
            formatter.begin_array(writer)?;
            let mut first = true;
            for v in a {
                formatter.begin_array_value(writer, first)?;
                write_value(writer, formatter, v)?;
                formatter.end_array_value(writer)?;
                first = false;
            }
            formatter.end_array(writer)
        }
        Value::Object(o) => {
            formatter.begin_object(writer)?;
            let mut first = true;
            for (k, v) in o {
                formatter.begin_object_key(writer, first)?;
                format_escaped_str(writer, formatter, k)?;
                formatter.end_object_key(writer)?;
                formatter.begin_object_value(writer)?;
                write_value(writer, formatter, v)?;
                formatter.end_object_value(writer)?;
                first = false;
            }
            formatter.end_object(writer)
        }
    }
}

/// Serializes a [`Value`] into an [`io::Write`] with an explicit formatter.
pub fn to_writer_with_formatter<W, F>(writer: &mut W, formatter: &mut F, value: &Value) -> Result<()>
where
    W: ?Sized + io::Write,
    F: ?Sized + Formatter,
{
    write_value(writer, formatter, value).map_err(Error::io)
}

/// Serializes a [`Value`] as compact JSON into an [`io::Write`].
pub fn to_writer<W>(writer: &mut W, value: &Value) -> Result<()>
where
    W: ?Sized + io::Write,
{
    to_writer_with_formatter(writer, &mut CompactFormatter, value)
}

/// Serializes a [`Value`] as pretty-printed JSON into an [`io::Write`].
pub fn to_writer_pretty<W>(writer: &mut W, value: &Value) -> Result<()>
where
    W: ?Sized + io::Write,
{
    to_writer_with_formatter(writer, &mut PrettyFormatter::new(), value)
}

/// Serializes a [`Value`] as a compact JSON byte vector.
pub fn to_vec(value: &Value) -> Result<Vec<u8>> {
    let mut out = Vec::with_capacity(128);
    to_writer(&mut out, value)?;
    Ok(out)
}

/// Serializes a [`Value`] as a pretty-printed JSON byte vector.
pub fn to_vec_pretty(value: &Value) -> Result<Vec<u8>> {
    let mut out = Vec::with_capacity(128);
    to_writer_pretty(&mut out, value)?;
    Ok(out)
}

/// Serializes a [`Value`] as a compact JSON string.
pub fn to_string(value: &Value) -> Result<String> {
    let vec = to_vec(value)?;
    // Every byte the formatter emits is either ASCII or a fragment copied out
    // of a `&str`, so the result is UTF-8 by construction.
    Ok(String::from_utf8(vec).unwrap_or_default())
}

/// Serializes a [`Value`] as a pretty-printed JSON string.
pub fn to_string_pretty(value: &Value) -> Result<String> {
    let vec = to_vec_pretty(value)?;
    Ok(String::from_utf8(vec).unwrap_or_default())
}

/// Serializes a [`Map`] the way an object value is serialized. Exists so a
/// caller holding a bare map does not have to wrap it in a [`Value`].
pub fn map_to_string(map: &Map<String, Value>) -> Result<String> {
    to_string(&Value::Object(map.clone()))
}
