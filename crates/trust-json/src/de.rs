// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The JSON parser.
//!
//! # Why this reproduces the incumbent's *imprecise* float parse on purpose
//!
//! `serde_json` has a `float_roundtrip` feature that swaps in a correctly-
//! rounded decimal-to-binary conversion. **This tree does not enable it** — the
//! only non-default `serde_json` feature anywhere in `crates/` is
//! `unbounded_depth`, at `crates/trust-types/Cargo.toml:49`. So the incumbent's
//! live behaviour is the default path: accumulate the significand into a `u64`,
//! then multiply or divide by a table of `f64` powers of ten. That path is off
//! by an ULP on plenty of inputs.
//!
//! A "better" parser here would be a REGRESSION: `parse -> serialize` is how
//! this tree moves proof bundles between processes, so a parser that lands on a
//! different `f64` than the incumbent changes the bytes on the way back out,
//! and every digest with it. The algorithm below is therefore a transcription,
//! including:
//!
//! * `POW10` as 309 **literals**, not a computed table. `1e100` written as a
//!   literal is the correctly-rounded `f64` nearest to 10^100; ten repeated
//!   multiplications by `10.0` is a different, drifted value. Generating this
//!   table with a loop silently changes results for large exponents.
//! * the `u64` significand overflow cut-over, which simply DISCARDS the digits
//!   past the overflow point (`parse_decimal_overflow`);
//! * `1e400` being an error (`number out of range`) while `1e-400` is `0.0`;
//! * `-0` parsing to the FLOAT `-0.0` rather than an integer, because negating
//!   a zero significand in the signed domain lands back on a non-negative
//!   value.
//!
//! The last of those is the kind of thing that only a differential finds: it is
//! not written down anywhere, it falls out of `parse_number`'s `if neg >= 0`.

use crate::error::{Error, ErrorCode, Result};
use crate::map::Map;
use crate::number::{N, Number};
use crate::value::Value;

/// The incumbent's default nesting limit.
const DEFAULT_RECURSION_LIMIT: u8 = 128;

/// A JSON parser over an in-memory slice.
pub struct Deserializer<'a> {
    slice: &'a [u8],
    index: usize,
    remaining_depth: u8,
    recursion_limit: bool,
}

enum ParserNumber {
    F64(f64),
    U64(u64),
    I64(i64),
}

impl ParserNumber {
    fn into_value(self) -> Value {
        Value::Number(match self {
            ParserNumber::F64(f) => Number { n: N::Float(f) },
            ParserNumber::U64(u) => Number { n: N::PosInt(u) },
            ParserNumber::I64(i) => Number { n: N::NegInt(i) },
        })
    }
}

impl<'a> Deserializer<'a> {
    #[must_use]
    pub fn from_slice(slice: &'a [u8]) -> Self {
        Deserializer {
            slice,
            index: 0,
            remaining_depth: DEFAULT_RECURSION_LIMIT,
            recursion_limit: true,
        }
    }

    #[must_use]
    pub fn from_str(s: &'a str) -> Self {
        Deserializer::from_slice(s.as_bytes())
    }

    /// Parses arbitrarily deep JSON without the 128-nesting-level guard.
    ///
    /// Mirrors the incumbent's `unbounded_depth` entry point, which
    /// `crates/trust-types/src/json_depth.rs:122` uses. Deep input can then
    /// overflow the stack; that is the caller's trade, exactly as it is with
    /// the incumbent.
    #[must_use]
    pub fn disable_recursion_limit(mut self) -> Self {
        self.recursion_limit = false;
        self
    }

    // -- byte-level cursor ---------------------------------------------------

    fn peek(&self) -> Option<u8> {
        self.slice.get(self.index).copied()
    }

    fn peek_or_null(&self) -> u8 {
        self.peek().unwrap_or(0)
    }

    fn next_char(&mut self) -> Option<u8> {
        let b = self.peek();
        if b.is_some() {
            self.index += 1;
        }
        b
    }

    fn eat_char(&mut self) {
        self.index += 1;
    }

    /// Returns the first non-whitespace byte WITHOUT consuming it.
    ///
    /// JSON whitespace is exactly these four bytes — not `char::is_whitespace`,
    /// which would also accept a form feed and U+00A0.
    fn parse_whitespace(&mut self) -> Option<u8> {
        loop {
            match self.peek() {
                Some(b' ' | b'\n' | b'\t' | b'\r') => self.eat_char(),
                other => return other,
            }
        }
    }

    // -- positions -----------------------------------------------------------

    /// Transcribed from the incumbent's `SliceRead::position_of_index`. Note
    /// the column is `i - start_of_line`, i.e. the count of bytes consumed on
    /// the line, which reads as 1-based for the byte just consumed and as
    /// 0-based for a peeked one — hence the two constructors below.
    fn position_of_index(&self, i: usize) -> (usize, usize) {
        let head = &self.slice[..i.min(self.slice.len())];
        let start_of_line = match head.iter().rposition(|&b| b == b'\n') {
            Some(p) => p + 1,
            None => 0,
        };
        let line = 1 + self.slice[..start_of_line]
            .iter()
            .filter(|&&b| b == b'\n')
            .count();
        (line, i.min(self.slice.len()) - start_of_line)
    }

    fn error(&self, code: ErrorCode) -> Error {
        let (line, column) = self.position_of_index(self.index);
        Error::syntax(code, line, column)
    }

    /// Error caused by a byte from `peek()`.
    fn peek_error(&self, code: ErrorCode) -> Error {
        let (line, column) = self.position_of_index(self.slice.len().min(self.index + 1));
        Error::syntax(code, line, column)
    }

    // -- values --------------------------------------------------------------

    /// Parses one JSON value, leaving the cursor after it.
    pub fn parse_value(&mut self) -> Result<Value> {
        let peek = match self.parse_whitespace() {
            Some(b) => b,
            None => return Err(self.peek_error(ErrorCode::EofWhileParsingValue)),
        };
        match peek {
            b'n' => {
                self.eat_char();
                self.parse_ident(b"ull")?;
                Ok(Value::Null)
            }
            b't' => {
                self.eat_char();
                self.parse_ident(b"rue")?;
                Ok(Value::Bool(true))
            }
            b'f' => {
                self.eat_char();
                self.parse_ident(b"alse")?;
                Ok(Value::Bool(false))
            }
            b'-' => {
                self.eat_char();
                Ok(self.parse_integer(false)?.into_value())
            }
            b'0'..=b'9' => Ok(self.parse_integer(true)?.into_value()),
            b'"' => {
                self.eat_char();
                Ok(Value::String(self.parse_str()?))
            }
            // The depth check happens BEFORE the bracket is consumed. That is
            // not cosmetic: `peek_error` reports `index + 1`, so eating first
            // would put the "recursion limit exceeded" column one past the
            // incumbent's. Caught by the differential, not by inspection.
            b'[' => {
                self.descend()?;
                self.eat_char();
                let r = self.parse_array();
                self.ascend();
                r
            }
            b'{' => {
                self.descend()?;
                self.eat_char();
                let r = self.parse_object();
                self.ascend();
                r
            }
            _ => Err(self.peek_error(ErrorCode::ExpectedSomeValue)),
        }
    }

    fn descend(&mut self) -> Result<()> {
        if !self.recursion_limit {
            return Ok(());
        }
        self.remaining_depth -= 1;
        if self.remaining_depth == 0 {
            self.remaining_depth += 1;
            return Err(self.peek_error(ErrorCode::RecursionLimitExceeded));
        }
        Ok(())
    }

    fn ascend(&mut self) {
        if self.recursion_limit {
            self.remaining_depth += 1;
        }
    }

    fn parse_ident(&mut self, ident: &[u8]) -> Result<()> {
        for expected in ident {
            match self.next_char() {
                None => return Err(self.error(ErrorCode::EofWhileParsingValue)),
                Some(next) => {
                    if next != *expected {
                        return Err(self.error(ErrorCode::ExpectedSomeIdent));
                    }
                }
            }
        }
        Ok(())
    }

    fn parse_array(&mut self) -> Result<Value> {
        let mut out = Vec::new();
        match self.parse_whitespace() {
            None => return Err(self.peek_error(ErrorCode::EofWhileParsingList)),
            Some(b']') => {
                self.eat_char();
                return Ok(Value::Array(out));
            }
            Some(_) => {}
        }
        loop {
            out.push(self.parse_value()?);
            match self.parse_whitespace() {
                None => return Err(self.peek_error(ErrorCode::EofWhileParsingList)),
                Some(b']') => {
                    self.eat_char();
                    return Ok(Value::Array(out));
                }
                Some(b',') => {
                    self.eat_char();
                    match self.parse_whitespace() {
                        None => return Err(self.peek_error(ErrorCode::EofWhileParsingValue)),
                        Some(b']') => return Err(self.peek_error(ErrorCode::TrailingComma)),
                        Some(_) => {}
                    }
                }
                Some(_) => return Err(self.peek_error(ErrorCode::ExpectedListCommaOrEnd)),
            }
        }
    }

    fn parse_object(&mut self) -> Result<Value> {
        let mut out = Map::new();
        match self.parse_whitespace() {
            None => return Err(self.peek_error(ErrorCode::EofWhileParsingObject)),
            Some(b'}') => {
                self.eat_char();
                return Ok(Value::Object(out));
            }
            Some(b'"') => {}
            Some(_) => return Err(self.peek_error(ErrorCode::KeyMustBeAString)),
        }
        loop {
            self.eat_char(); // the opening quote
            let key = self.parse_str()?;
            match self.parse_whitespace() {
                None => return Err(self.peek_error(ErrorCode::EofWhileParsingObject)),
                Some(b':') => self.eat_char(),
                Some(_) => return Err(self.peek_error(ErrorCode::ExpectedColon)),
            }
            let value = self.parse_value()?;
            // Last key wins on a duplicate — the incumbent's behaviour, and a
            // deliberate non-error: `{"a":1,"a":2}` parses to `{"a":2}`.
            out.insert(key, value);
            match self.parse_whitespace() {
                None => return Err(self.peek_error(ErrorCode::EofWhileParsingObject)),
                Some(b'}') => {
                    self.eat_char();
                    return Ok(Value::Object(out));
                }
                Some(b',') => {
                    self.eat_char();
                    match self.parse_whitespace() {
                        None => return Err(self.peek_error(ErrorCode::EofWhileParsingValue)),
                        Some(b'"') => {}
                        Some(b'}') => return Err(self.peek_error(ErrorCode::TrailingComma)),
                        Some(_) => return Err(self.peek_error(ErrorCode::KeyMustBeAString)),
                    }
                }
                Some(_) => return Err(self.peek_error(ErrorCode::ExpectedObjectCommaOrEnd)),
            }
        }
    }

    // -- strings -------------------------------------------------------------

    /// Parses the body of a string; the opening quote is already consumed.
    fn parse_str(&mut self) -> Result<String> {
        let mut scratch: Vec<u8> = Vec::new();
        let start = self.index;
        loop {
            let Some(byte) = self.peek() else {
                self.index = self.slice.len();
                return Err(self.error(ErrorCode::EofWhileParsingString));
            };
            match byte {
                b'"' => {
                    scratch.extend_from_slice(&self.slice[start..self.index]);
                    self.eat_char();
                    return finish_utf8(scratch, self);
                }
                b'\\' => {
                    scratch.extend_from_slice(&self.slice[start..self.index]);
                    self.eat_char();
                    self.parse_escape(&mut scratch)?;
                    return self.parse_str_tail(scratch);
                }
                0x00..=0x1F => {
                    return Err(self.peek_error(ErrorCode::ControlCharacterWhileParsingString));
                }
                _ => self.eat_char(),
            }
        }
    }

    /// The same loop once an escape has forced a copy into `scratch`.
    fn parse_str_tail(&mut self, mut scratch: Vec<u8>) -> Result<String> {
        loop {
            let start = self.index;
            loop {
                let Some(byte) = self.peek() else {
                    self.index = self.slice.len();
                    return Err(self.error(ErrorCode::EofWhileParsingString));
                };
                match byte {
                    b'"' => {
                        scratch.extend_from_slice(&self.slice[start..self.index]);
                        self.eat_char();
                        return finish_utf8(scratch, self);
                    }
                    b'\\' => {
                        scratch.extend_from_slice(&self.slice[start..self.index]);
                        self.eat_char();
                        self.parse_escape(&mut scratch)?;
                        break;
                    }
                    0x00..=0x1F => {
                        return Err(self.peek_error(ErrorCode::ControlCharacterWhileParsingString));
                    }
                    _ => self.eat_char(),
                }
            }
        }
    }

    fn parse_escape(&mut self, scratch: &mut Vec<u8>) -> Result<()> {
        let ch = match self.next_char() {
            Some(c) => c,
            None => return Err(self.error(ErrorCode::EofWhileParsingString)),
        };
        match ch {
            b'"' => scratch.push(b'"'),
            b'\\' => scratch.push(b'\\'),
            b'/' => scratch.push(b'/'),
            b'b' => scratch.push(0x08),
            b'f' => scratch.push(0x0C),
            b'n' => scratch.push(b'\n'),
            b'r' => scratch.push(b'\r'),
            b't' => scratch.push(b'\t'),
            b'u' => {
                let c = match self.decode_hex_escape()? {
                    // A trailing surrogate with no leading one. The incumbent
                    // reports it with the LEADING-surrogate code; transcribed,
                    // not corrected, because the text is user-visible.
                    0xDC00..=0xDFFF => {
                        return Err(self.error(ErrorCode::LoneLeadingSurrogateInHexEscape));
                    }
                    n1 @ 0xD800..=0xDBFF => {
                        // The incumbent reads these two bytes with `peek_or_eof`,
                        // NOT `peek_or_null`: at end of input it reports
                        // `EofWhileParsingString` (`Category::Eof`, so
                        // `Error::is_eof()` is true) and never reaches the
                        // not-a-backslash branch. `peek_or_null` turns EOF into a
                        // 0 byte, which falls through to
                        // `UnexpectedEndOfHexEscape` (`Category::Syntax`) — same
                        // column, different code, text and category. The number
                        // paths above DO use `peek_or_null`, which is why this is
                        // easy to get wrong.
                        match self.peek() {
                            Some(b'\\') => self.eat_char(),
                            Some(_) => {
                                self.eat_char();
                                return Err(self.error(ErrorCode::UnexpectedEndOfHexEscape));
                            }
                            None => {
                                return Err(self.error(ErrorCode::EofWhileParsingString));
                            }
                        }
                        match self.peek() {
                            Some(b'u') => self.eat_char(),
                            Some(_) => {
                                self.eat_char();
                                return Err(self.error(ErrorCode::UnexpectedEndOfHexEscape));
                            }
                            None => {
                                return Err(self.error(ErrorCode::EofWhileParsingString));
                            }
                        }
                        let n2 = self.decode_hex_escape()?;
                        if !(0xDC00..=0xDFFF).contains(&n2) {
                            return Err(self.error(ErrorCode::LoneLeadingSurrogateInHexEscape));
                        }
                        let n = ((u32::from(n1 - 0xD800) << 10) | u32::from(n2 - 0xDC00)) + 0x1_0000;
                        match char::from_u32(n) {
                            Some(c) => c,
                            None => return Err(self.error(ErrorCode::InvalidUnicodeCodePoint)),
                        }
                    }
                    n => match char::from_u32(u32::from(n)) {
                        Some(c) => c,
                        None => return Err(self.error(ErrorCode::InvalidUnicodeCodePoint)),
                    },
                };
                scratch.extend_from_slice(c.encode_utf8(&mut [0u8; 4]).as_bytes());
            }
            _ => return Err(self.error(ErrorCode::InvalidEscape)),
        }
        Ok(())
    }

    /// Four hex digits after `\u`.
    ///
    /// The incumbent CONSUMES all four bytes and only then validates them, so
    /// an `invalid escape` on `"\uZZZZ"` is reported four columns further along
    /// than a validate-first reader would report it. Transcribed, because the
    /// column is user-visible. Fewer than four bytes left is a different code
    /// (`EOF while parsing a string`) reported at end-of-input.
    fn decode_hex_escape(&mut self) -> Result<u16> {
        if self.index + 4 > self.slice.len() {
            self.index = self.slice.len();
            return Err(self.error(ErrorCode::EofWhileParsingString));
        }
        let digits = [
            self.slice[self.index],
            self.slice[self.index + 1],
            self.slice[self.index + 2],
            self.slice[self.index + 3],
        ];
        self.index += 4;
        let mut n: u16 = 0;
        for b in digits {
            let d = match b {
                b'0'..=b'9' => u16::from(b - b'0'),
                b'a'..=b'f' => u16::from(b - b'a') + 10,
                b'A'..=b'F' => u16::from(b - b'A') + 10,
                _ => return Err(self.error(ErrorCode::InvalidEscape)),
            };
            n = n * 16 + d;
        }
        Ok(n)
    }

    // -- numbers -------------------------------------------------------------

    fn parse_integer(&mut self, positive: bool) -> Result<ParserNumber> {
        let next = match self.next_char() {
            Some(b) => b,
            None => return Err(self.error(ErrorCode::EofWhileParsingValue)),
        };
        match next {
            b'0' => {
                // There can be only one leading `0`.
                match self.peek_or_null() {
                    b'0'..=b'9' => Err(self.peek_error(ErrorCode::InvalidNumber)),
                    _ => self.parse_number(positive, 0),
                }
            }
            c @ b'1'..=b'9' => {
                let mut significand = u64::from(c - b'0');
                loop {
                    match self.peek_or_null() {
                        c @ b'0'..=b'9' => {
                            let digit = u64::from(c - b'0');
                            // Once a `u64` cannot hold the significand any
                            // more, the incumbent stops accumulating and
                            // switches to a float, DISCARDING the rest.
                            if significand > (u64::MAX - digit) / 10 {
                                return Ok(ParserNumber::F64(
                                    self.parse_long_integer(positive, significand)?,
                                ));
                            }
                            self.eat_char();
                            significand = significand * 10 + digit;
                        }
                        _ => return self.parse_number(positive, significand),
                    }
                }
            }
            _ => Err(self.error(ErrorCode::InvalidNumber)),
        }
    }

    fn parse_number(&mut self, positive: bool, significand: u64) -> Result<ParserNumber> {
        Ok(match self.peek_or_null() {
            b'.' => ParserNumber::F64(self.parse_decimal(positive, significand, 0)?),
            b'e' | b'E' => ParserNumber::F64(self.parse_exponent(positive, significand, 0)?),
            _ => {
                if positive {
                    ParserNumber::U64(significand)
                } else {
                    let neg = (significand as i64).wrapping_neg();
                    // This is where `-0` becomes the FLOAT `-0.0`: negating a
                    // zero significand lands on a non-negative value.
                    if neg >= 0 {
                        ParserNumber::F64(-(significand as f64))
                    } else {
                        ParserNumber::I64(neg)
                    }
                }
            }
        })
    }

    fn parse_decimal(
        &mut self,
        positive: bool,
        mut significand: u64,
        exponent_before_decimal_point: i32,
    ) -> Result<f64> {
        self.eat_char();
        let mut exponent_after_decimal_point = 0;
        while let c @ b'0'..=b'9' = self.peek_or_null() {
            let digit = u64::from(c - b'0');
            if significand > (u64::MAX - digit) / 10 {
                let exponent = exponent_before_decimal_point + exponent_after_decimal_point;
                return self.parse_decimal_overflow(positive, significand, exponent);
            }
            self.eat_char();
            significand = significand * 10 + digit;
            exponent_after_decimal_point -= 1;
        }
        if exponent_after_decimal_point == 0 {
            return match self.peek() {
                Some(_) => Err(self.peek_error(ErrorCode::InvalidNumber)),
                None => Err(self.peek_error(ErrorCode::EofWhileParsingValue)),
            };
        }
        let exponent = exponent_before_decimal_point + exponent_after_decimal_point;
        match self.peek_or_null() {
            b'e' | b'E' => self.parse_exponent(positive, significand, exponent),
            _ => self.f64_from_parts(positive, significand, exponent),
        }
    }

    fn parse_exponent(
        &mut self,
        positive: bool,
        significand: u64,
        starting_exp: i32,
    ) -> Result<f64> {
        self.eat_char();
        let positive_exp = match self.peek_or_null() {
            b'+' => {
                self.eat_char();
                true
            }
            b'-' => {
                self.eat_char();
                false
            }
            _ => true,
        };
        let next = match self.next_char() {
            Some(b) => b,
            None => return Err(self.error(ErrorCode::EofWhileParsingValue)),
        };
        let mut exp = match next {
            c @ b'0'..=b'9' => i32::from(c - b'0'),
            _ => return Err(self.error(ErrorCode::InvalidNumber)),
        };
        while let c @ b'0'..=b'9' = self.peek_or_null() {
            self.eat_char();
            let digit = i32::from(c - b'0');
            if exp > (i32::MAX - digit) / 10 {
                let zero_significand = significand == 0;
                return self.parse_exponent_overflow(positive, zero_significand, positive_exp);
            }
            exp = exp * 10 + digit;
        }
        let final_exp = if positive_exp {
            starting_exp.saturating_add(exp)
        } else {
            starting_exp.saturating_sub(exp)
        };
        self.f64_from_parts(positive, significand, final_exp)
    }

    fn parse_long_integer(&mut self, positive: bool, significand: u64) -> Result<f64> {
        let mut exponent = 0;
        loop {
            match self.peek_or_null() {
                b'0'..=b'9' => {
                    self.eat_char();
                    exponent += 1;
                }
                b'.' => return self.parse_decimal(positive, significand, exponent),
                b'e' | b'E' => return self.parse_exponent(positive, significand, exponent),
                _ => return self.f64_from_parts(positive, significand, exponent),
            }
        }
    }

    fn parse_decimal_overflow(
        &mut self,
        positive: bool,
        significand: u64,
        exponent: i32,
    ) -> Result<f64> {
        // The next multiply/add would overflow, so all further digits are
        // simply dropped. This is lossy, and it is the shipped behaviour.
        while let b'0'..=b'9' = self.peek_or_null() {
            self.eat_char();
        }
        match self.peek_or_null() {
            b'e' | b'E' => self.parse_exponent(positive, significand, exponent),
            _ => self.f64_from_parts(positive, significand, exponent),
        }
    }

    fn parse_exponent_overflow(
        &mut self,
        positive: bool,
        zero_significand: bool,
        positive_exp: bool,
    ) -> Result<f64> {
        // Error instead of +/- infinity.
        if !zero_significand && positive_exp {
            return Err(self.error(ErrorCode::NumberOutOfRange));
        }
        while let b'0'..=b'9' = self.peek_or_null() {
            self.eat_char();
        }
        Ok(if positive { 0.0 } else { -0.0 })
    }

    fn f64_from_parts(
        &mut self,
        positive: bool,
        significand: u64,
        mut exponent: i32,
    ) -> Result<f64> {
        let mut f = significand as f64;
        loop {
            match POW10.get(exponent.unsigned_abs() as usize) {
                Some(&pow) => {
                    if exponent >= 0 {
                        f *= pow;
                        if f.is_infinite() {
                            return Err(self.error(ErrorCode::NumberOutOfRange));
                        }
                    } else {
                        f /= pow;
                    }
                    break;
                }
                None => {
                    if f == 0.0 {
                        break;
                    }
                    if exponent >= 0 {
                        return Err(self.error(ErrorCode::NumberOutOfRange));
                    }
                    f /= 1e308;
                    exponent += 308;
                }
            }
        }
        Ok(if positive { f } else { -f })
    }

    /// Consumes trailing whitespace and errors if anything else is left.
    pub fn end(&mut self) -> Result<()> {
        match self.parse_whitespace() {
            Some(_) => Err(self.peek_error(ErrorCode::TrailingCharacters)),
            None => Ok(()),
        }
    }
}

fn finish_utf8(scratch: Vec<u8>, de: &Deserializer<'_>) -> Result<String> {
    String::from_utf8(scratch).map_err(|_| de.error(ErrorCode::InvalidUnicodeCodePoint))
}

/// Deserializes an instance of [`Value`] from a string of JSON text.
pub fn from_str(s: &str) -> Result<Value> {
    let mut de = Deserializer::from_str(s);
    let value = de.parse_value()?;
    de.end()?;
    Ok(value)
}

/// Deserializes an instance of [`Value`] from bytes of JSON text.
pub fn from_slice(v: &[u8]) -> Result<Value> {
    let mut de = Deserializer::from_slice(v);
    let value = de.parse_value()?;
    de.end()?;
    Ok(value)
}

/// The incumbent's `POW10`, as LITERALS. See the module docs: a computed table
/// is a different table.
#[rustfmt::skip]
static POW10: [f64; 309] = [
    1e000, 1e001, 1e002, 1e003, 1e004, 1e005, 1e006, 1e007, 1e008, 1e009,
    1e010, 1e011, 1e012, 1e013, 1e014, 1e015, 1e016, 1e017, 1e018, 1e019,
    1e020, 1e021, 1e022, 1e023, 1e024, 1e025, 1e026, 1e027, 1e028, 1e029,
    1e030, 1e031, 1e032, 1e033, 1e034, 1e035, 1e036, 1e037, 1e038, 1e039,
    1e040, 1e041, 1e042, 1e043, 1e044, 1e045, 1e046, 1e047, 1e048, 1e049,
    1e050, 1e051, 1e052, 1e053, 1e054, 1e055, 1e056, 1e057, 1e058, 1e059,
    1e060, 1e061, 1e062, 1e063, 1e064, 1e065, 1e066, 1e067, 1e068, 1e069,
    1e070, 1e071, 1e072, 1e073, 1e074, 1e075, 1e076, 1e077, 1e078, 1e079,
    1e080, 1e081, 1e082, 1e083, 1e084, 1e085, 1e086, 1e087, 1e088, 1e089,
    1e090, 1e091, 1e092, 1e093, 1e094, 1e095, 1e096, 1e097, 1e098, 1e099,
    1e100, 1e101, 1e102, 1e103, 1e104, 1e105, 1e106, 1e107, 1e108, 1e109,
    1e110, 1e111, 1e112, 1e113, 1e114, 1e115, 1e116, 1e117, 1e118, 1e119,
    1e120, 1e121, 1e122, 1e123, 1e124, 1e125, 1e126, 1e127, 1e128, 1e129,
    1e130, 1e131, 1e132, 1e133, 1e134, 1e135, 1e136, 1e137, 1e138, 1e139,
    1e140, 1e141, 1e142, 1e143, 1e144, 1e145, 1e146, 1e147, 1e148, 1e149,
    1e150, 1e151, 1e152, 1e153, 1e154, 1e155, 1e156, 1e157, 1e158, 1e159,
    1e160, 1e161, 1e162, 1e163, 1e164, 1e165, 1e166, 1e167, 1e168, 1e169,
    1e170, 1e171, 1e172, 1e173, 1e174, 1e175, 1e176, 1e177, 1e178, 1e179,
    1e180, 1e181, 1e182, 1e183, 1e184, 1e185, 1e186, 1e187, 1e188, 1e189,
    1e190, 1e191, 1e192, 1e193, 1e194, 1e195, 1e196, 1e197, 1e198, 1e199,
    1e200, 1e201, 1e202, 1e203, 1e204, 1e205, 1e206, 1e207, 1e208, 1e209,
    1e210, 1e211, 1e212, 1e213, 1e214, 1e215, 1e216, 1e217, 1e218, 1e219,
    1e220, 1e221, 1e222, 1e223, 1e224, 1e225, 1e226, 1e227, 1e228, 1e229,
    1e230, 1e231, 1e232, 1e233, 1e234, 1e235, 1e236, 1e237, 1e238, 1e239,
    1e240, 1e241, 1e242, 1e243, 1e244, 1e245, 1e246, 1e247, 1e248, 1e249,
    1e250, 1e251, 1e252, 1e253, 1e254, 1e255, 1e256, 1e257, 1e258, 1e259,
    1e260, 1e261, 1e262, 1e263, 1e264, 1e265, 1e266, 1e267, 1e268, 1e269,
    1e270, 1e271, 1e272, 1e273, 1e274, 1e275, 1e276, 1e277, 1e278, 1e279,
    1e280, 1e281, 1e282, 1e283, 1e284, 1e285, 1e286, 1e287, 1e288, 1e289,
    1e290, 1e291, 1e292, 1e293, 1e294, 1e295, 1e296, 1e297, 1e298, 1e299,
    1e300, 1e301, 1e302, 1e303, 1e304, 1e305, 1e306, 1e307, 1e308,
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn minus_zero_is_a_float() {
        // Falls out of `parse_number`'s `if neg >= 0`. Nothing documents it.
        let v = from_str("-0").unwrap();
        assert!(v.is_f64(), "expected f64, got {v:?}");
        assert_eq!(v.to_string(), "-0.0");
        // ... while a plain `0` stays an integer.
        assert!(from_str("0").unwrap().is_u64());
    }

    #[test]
    fn integer_width_cutovers() {
        assert!(from_str("9223372036854775807").unwrap().is_i64());
        assert!(from_str("9223372036854775808").unwrap().is_u64());
        assert!(!from_str("9223372036854775808").unwrap().is_i64());
        assert!(from_str("18446744073709551615").unwrap().is_u64());
        assert!(from_str("18446744073709551616").unwrap().is_f64());
        assert!(from_str("-9223372036854775808").unwrap().is_i64());
        assert!(from_str("-9223372036854775809").unwrap().is_f64());
    }

    #[test]
    fn range_errors_are_one_sided() {
        assert!(from_str("1e400").is_err());
        assert!(from_str("-1e400").is_err());
        // Underflow is NOT an error; it is zero.
        assert_eq!(from_str("1e-400").unwrap().to_string(), "0.0");
    }

    #[test]
    fn duplicate_keys_take_the_last() {
        assert_eq!(from_str(r#"{"a":1,"a":2}"#).unwrap().to_string(), r#"{"a":2}"#);
    }

    #[test]
    fn recursion_limit_is_128_and_can_be_lifted() {
        let deep = "[".repeat(200) + &"]".repeat(200);
        assert!(from_str(&deep).is_err());
        let mut de = Deserializer::from_str(&deep).disable_recursion_limit();
        assert!(de.parse_value().is_ok());
    }
}
