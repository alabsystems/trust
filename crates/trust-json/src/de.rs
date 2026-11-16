// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The JSON parser.
//!
//! # Floats are parsed with correct rounding, because the incumbent's are
//!
//! `serde_json` has two float parsers. The default one accumulates the
//! significand into a `u64`, then multiplies or divides by a table of `f64`
//! powers of ten, and is off by an ULP on plenty of inputs; its
//! `float_roundtrip` feature swaps in a correctly-rounded conversion. **This
//! workspace enables `float_roundtrip`**: first-party/clean's
//! `crates/clean-olean/Cargo.toml` names it (clean 99ddfe452), and Cargo
//! feature unification turns it on for every `serde_json` in a build graph that
//! contains clean-olean. So the live incumbent returns the IEEE-754 double
//! nearest to the decimal text, ties to even.
//!
//! `parse -> serialize` is how this tree moves proof bundles between
//! processes, so a parser that lands on a different `f64` than the incumbent
//! changes the bytes on the way back out, and every digest with it. Correct
//! rounding has exactly one answer per input, so this parser does not copy the
//! incumbent's algorithm (serde_json's vendored lexical: extended-float with a
//! big-integer fallback). Short significands take Clinger's exact fast path
//! (below 2^53, power of ten up to 10^22, `POW10_EXACT`); everything else is
//! handed to `core`'s `f64::from_str`, which is also correctly rounded. What is
//! kept from the incumbent is the GRAMMAR and the error behaviour, including:
//!
//! * the `u64` significand overflow cut-over, after which the FULL digit text
//!   is converted (`parse_long_integer`, `parse_decimal_overflow`) — the
//!   default incumbent path discarded those digits, the correctly-rounded one
//!   does not;
//! * `1e400` being an error (`number out of range`) while `1e-400` is `0.0`;
//! * `-0` parsing to the FLOAT `-0.0` rather than an integer, because negating
//!   a zero significand in the signed domain lands back on a non-negative
//!   value.
//!
//! The last of those is the kind of thing that only a differential finds: it is
//! not written down anywhere, it falls out of `parse_number`'s `if neg >= 0`.
//! `tests/differential_json.rs::oracle_identity` asserts the incumbent's parse
//! mode with a `1e-30` sentinel, so a change of mode fails with its reason.

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
    /// Index of the first digit of the number being parsed (after any `-`).
    /// The long paths convert `slice[number_start..index]` as text.
    number_start: usize,
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
            number_start: 0,
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
        let line = 1 + self.slice[..start_of_line].iter().filter(|&&b| b == b'\n').count();
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
                        let n =
                            ((u32::from(n1 - 0xD800) << 10) | u32::from(n2 - 0xDC00)) + 0x1_0000;
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
        self.number_start = self.index;
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
                            // switches to converting the whole digit text.
                            if significand > (u64::MAX - digit) / 10 {
                                return Ok(ParserNumber::F64(self.parse_long_integer(positive)?));
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
                return self.parse_decimal_overflow(positive, exponent);
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

    /// The significand no longer fits a `u64`: keep consuming digits and
    /// convert the whole text. Only reached from `parse_integer`, so no `.`
    /// has been seen yet.
    fn parse_long_integer(&mut self, positive: bool) -> Result<f64> {
        loop {
            match self.peek_or_null() {
                b'0'..=b'9' => self.eat_char(),
                b'.' => {
                    self.eat_char();
                    return self.parse_long_decimal(positive, false);
                }
                b'e' | b'E' => return self.parse_long_exponent(positive),
                _ => return self.f64_long_from_text(positive),
            }
        }
    }

    /// The significand overflowed inside the fraction. `exponent` is minus
    /// the number of fraction digits consumed so far; the significand itself
    /// is superseded by the text, as in the incumbent's `float_roundtrip`
    /// path.
    fn parse_decimal_overflow(&mut self, positive: bool, exponent: i32) -> Result<f64> {
        self.parse_long_decimal(positive, exponent < 0)
    }

    fn parse_long_decimal(&mut self, positive: bool, mut at_least_one_digit: bool) -> Result<f64> {
        while let b'0'..=b'9' = self.peek_or_null() {
            self.eat_char();
            at_least_one_digit = true;
        }
        if !at_least_one_digit {
            return match self.peek() {
                Some(_) => Err(self.peek_error(ErrorCode::InvalidNumber)),
                None => Err(self.peek_error(ErrorCode::EofWhileParsingValue)),
            };
        }
        match self.peek_or_null() {
            b'e' | b'E' => self.parse_long_exponent(positive),
            _ => self.f64_long_from_text(positive),
        }
    }

    fn parse_long_exponent(&mut self, positive: bool) -> Result<f64> {
        let mantissa_end = self.index;
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
                let zero_significand = self.slice[self.number_start..mantissa_end]
                    .iter()
                    .all(|&b| b == b'0' || b == b'.');
                return self.parse_exponent_overflow(positive, zero_significand, positive_exp);
            }
            exp = exp * 10 + digit;
        }
        self.f64_long_from_text(positive)
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

    /// Converts `slice[number_start..index]`, which the grammar above has
    /// already validated as `digits [. digits] [(e|E) [+|-] digits]`.
    fn f64_long_from_text(&mut self, positive: bool) -> Result<f64> {
        let text = &self.slice[self.number_start..self.index];
        let f = match core::str::from_utf8(text).ok().and_then(|t| t.parse::<f64>().ok()) {
            Some(f) => f,
            // Unreachable: the text is ASCII and matches `f64::from_str`'s
            // grammar. Reported rather than panicked on.
            None => return Err(self.error(ErrorCode::InvalidNumber)),
        };
        self.finish_float(positive, f)
    }

    fn f64_from_parts(&mut self, positive: bool, significand: u64, exponent: i32) -> Result<f64> {
        match concise_float(significand, exponent) {
            Some(f) => self.finish_float(positive, f),
            None => Err(self.error(ErrorCode::InvalidNumber)),
        }
    }

    fn finish_float(&self, positive: bool, f: f64) -> Result<f64> {
        if f.is_infinite() {
            Err(self.error(ErrorCode::NumberOutOfRange))
        } else {
            Ok(if positive { f } else { -f })
        }
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

/// The correctly-rounded `f64` nearest to `significand * 10^exponent`
/// (possibly infinite). `None` is unreachable: the text handed to
/// `f64::from_str` is always `<digits>e[-]<digits>`.
fn concise_float(significand: u64, exponent: i32) -> Option<f64> {
    if significand == 0 {
        return Some(0.0);
    }
    // Clinger's fast path: both operands are exact doubles, and a single IEEE
    // multiply or divide is correctly rounded.
    if significand >> 53 == 0 && (-22..=22).contains(&exponent) {
        let f = significand as f64;
        let pow = POW10_EXACT[exponent.unsigned_abs() as usize];
        return Some(if exponent >= 0 { f * pow } else { f / pow });
    }
    // `u64::MAX` is 20 digits and an `i32` exponent at most 10 digits plus a
    // sign, so 32 bytes always suffice.
    let mut buf = [0u8; 32];
    let mut len = push_decimal(&mut buf, 0, significand);
    buf[len] = b'e';
    len += 1;
    if exponent < 0 {
        buf[len] = b'-';
        len += 1;
    }
    len = push_decimal(&mut buf, len, u64::from(exponent.unsigned_abs()));
    core::str::from_utf8(&buf[..len]).ok()?.parse::<f64>().ok()
}

/// Writes `n` in decimal at `buf[at..]`; returns the new end.
fn push_decimal(buf: &mut [u8; 32], mut at: usize, mut n: u64) -> usize {
    let mut digits = [0u8; 20];
    let mut k = 0;
    loop {
        digits[k] = b'0' + (n % 10) as u8;
        k += 1;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    while k > 0 {
        k -= 1;
        buf[at] = digits[k];
        at += 1;
    }
    at
}

/// 10^0 ..= 10^22: every entry is exactly representable as an `f64`.
#[rustfmt::skip]
static POW10_EXACT: [f64; 23] = [
    1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11,
    1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22,
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

    fn bits(text: &str) -> u64 {
        from_str(text).unwrap().as_f64().unwrap().to_bits()
    }

    #[test]
    fn floats_are_correctly_rounded() {
        // Expected bits computed with exact rational arithmetic, rounded
        // half-to-even. The first four were each one ULP off under the old
        // pow10-table parse (`0x...c29f`, `...abeb`, `...7186`, `...6be9`).
        assert_eq!(bits("1e-30"), 0x39b4_484b_feeb_c2a0);
        assert_eq!(bits("6e49"), 0x4a44_86de_8697_abec);
        assert_eq!(bits("73226931040922149623.126525269250477665"), 0x440f_c1d2_8e78_7185);
        assert_eq!(bits("-1.0877008403719409e-197"), 0x970a_04a6_3cf0_6bea);
        assert_eq!(bits("3E91"), 0x52ed_745e_1896_c42b);
        assert_eq!(bits("7E81"), 0x50ed_84a5_c19f_92f0);
    }

    #[test]
    fn long_significands_keep_every_digit() {
        // The u64 overflow cut-over used to DISCARD the remaining digits.
        let ones = format!("{}.{}", "1".repeat(40), "7".repeat(40));
        assert_eq!(from_str(&ones).unwrap().to_string(), "1.1111111111111112e+39");
        let nines = format!("{}e-10", "9".repeat(100));
        assert_eq!(from_str(&nines).unwrap().to_string(), "1e+90");
        // Overflow inside the fraction, with a leading-zero integer part.
        let frac = format!("0.{}", "3".repeat(60));
        assert_eq!(from_str(&frac).unwrap().to_string(), "0.3333333333333333");
        assert_eq!(from_str(&format!("-{frac}")).unwrap().to_string(), "-0.3333333333333333");
        // Long-path range behaviour matches the short path.
        assert!(from_str(&format!("{}e400", "1".repeat(30))).is_err());
        assert!(from_str(&format!("{}e99999999999", "1".repeat(30))).is_err());
        assert_eq!(
            from_str(&format!("{}e-99999999999", "1".repeat(30))).unwrap().to_string(),
            "0.0"
        );
        // ... and so does its grammar.
        assert!(from_str(&format!("{}.", "1".repeat(30))).is_err());
        assert!(from_str(&format!("{}e", "1".repeat(30))).is_err());
        assert!(from_str(&format!("{}e+", "1".repeat(30))).is_err());
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
