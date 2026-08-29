// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A strict, minimal JSON reader for the golden fixture.
//!
//! WHY THIS IS HERE INSTEAD OF A DEPENDENCY: `trust-bincode` is a
//! dependency-retirement crate; its whole point is that the only third-party
//! edge is the `serde` trait ABI. Pulling a JSON crate in — even a
//! Trust-owned one — to read a test fixture would add a dev-edge to the very
//! graph being measured, and would couple this crate's acceptance gate to
//! another crate's parser.
//!
//! THE OBVIOUS FAILURE MODE OF A HAND-ROLLED PARSER is that it silently drops
//! cases and the differential reads green while testing less than it claims.
//! That is defended against in `golden_bincode1.rs`, not here: the test
//! asserts the exact observation counts recorded in the fixture's own
//! `counts` block (167 encode cases / 501 encode observations / 40 decode
//! cases / 317 decode observations) against what it actually checked. A
//! parser that skipped anything would fail on the count, not read clean.
//!
//! Numbers are kept as their raw source text, never routed through `f64`, so
//! no magnitude in the fixture can lose precision.

use std::collections::BTreeMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    /// The number's literal source text.
    Num(String),
    Str(String),
    Arr(Vec<Json>),
    Obj(BTreeMap<String, Json>),
}

impl Json {
    /// Object field lookup. Panics with the key name if absent — a missing
    /// field in the fixture is a test bug, and a silent `None` is exactly the
    /// silent-instrument failure this file warns about.
    pub fn get(&self, key: &str) -> &Json {
        match self {
            Json::Obj(m) => m
                .get(key)
                .unwrap_or_else(|| panic!("fixture: no key {key:?} in object; keys = {:?}", m.keys().collect::<Vec<_>>())),
            other => panic!("fixture: expected an object to read key {key:?}, got {other:?}"),
        }
    }

    pub fn try_get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(m) => m.get(key),
            _ => None,
        }
    }

    pub fn keys(&self) -> Vec<String> {
        match self {
            Json::Obj(m) => m.keys().cloned().collect(),
            other => panic!("fixture: expected an object, got {other:?}"),
        }
    }

    pub fn str(&self) -> &str {
        match self {
            Json::Str(s) => s,
            other => panic!("fixture: expected a string, got {other:?}"),
        }
    }

    pub fn arr(&self) -> &[Json] {
        match self {
            Json::Arr(v) => v,
            other => panic!("fixture: expected an array, got {other:?}"),
        }
    }

    pub fn bool(&self) -> bool {
        match self {
            Json::Bool(b) => *b,
            other => panic!("fixture: expected a bool, got {other:?}"),
        }
    }

    pub fn u64(&self) -> u64 {
        match self {
            Json::Num(n) => n
                .parse::<u64>()
                .unwrap_or_else(|e| panic!("fixture: {n:?} is not a u64: {e}")),
            other => panic!("fixture: expected a number, got {other:?}"),
        }
    }

    pub fn is_null(&self) -> bool {
        matches!(self, Json::Null)
    }
}

#[derive(Debug)]
pub struct ParseError {
    pub offset: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "JSON parse error at byte {}: {}", self.offset, self.message)
    }
}

pub fn parse(input: &str) -> Result<Json, ParseError> {
    let mut p = Parser {
        bytes: input.as_bytes(),
        pos: 0,
    };
    p.skip_ws();
    let v = p.value(0)?;
    p.skip_ws();
    if p.pos != p.bytes.len() {
        return Err(p.err("trailing content after the top-level value"));
    }
    Ok(v)
}

struct Parser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

/// Guards against a hostile/broken fixture eating the stack.
const MAX_DEPTH: usize = 64;

impl<'a> Parser<'a> {
    fn err(&self, message: &str) -> ParseError {
        ParseError {
            offset: self.pos,
            message: message.to_string(),
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn skip_ws(&mut self) {
        while let Some(b) = self.peek() {
            if b == b' ' || b == b'\t' || b == b'\n' || b == b'\r' {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn expect(&mut self, b: u8) -> Result<(), ParseError> {
        if self.peek() == Some(b) {
            self.pos += 1;
            Ok(())
        } else {
            Err(self.err(&format!("expected {:?}", b as char)))
        }
    }

    fn lit(&mut self, s: &str) -> Result<(), ParseError> {
        if self.bytes[self.pos..].starts_with(s.as_bytes()) {
            self.pos += s.len();
            Ok(())
        } else {
            Err(self.err(&format!("expected literal {s:?}")))
        }
    }

    fn value(&mut self, depth: usize) -> Result<Json, ParseError> {
        if depth > MAX_DEPTH {
            return Err(self.err("nesting deeper than the fixture reader allows"));
        }
        match self.peek() {
            None => Err(self.err("unexpected end of input")),
            Some(b'n') => {
                self.lit("null")?;
                Ok(Json::Null)
            }
            Some(b't') => {
                self.lit("true")?;
                Ok(Json::Bool(true))
            }
            Some(b'f') => {
                self.lit("false")?;
                Ok(Json::Bool(false))
            }
            Some(b'"') => Ok(Json::Str(self.string()?)),
            Some(b'[') => {
                self.pos += 1;
                let mut out = Vec::new();
                self.skip_ws();
                if self.peek() == Some(b']') {
                    self.pos += 1;
                    return Ok(Json::Arr(out));
                }
                loop {
                    self.skip_ws();
                    out.push(self.value(depth + 1)?);
                    self.skip_ws();
                    match self.peek() {
                        Some(b',') => self.pos += 1,
                        Some(b']') => {
                            self.pos += 1;
                            return Ok(Json::Arr(out));
                        }
                        _ => return Err(self.err("expected ',' or ']' in array")),
                    }
                }
            }
            Some(b'{') => {
                self.pos += 1;
                let mut out = BTreeMap::new();
                self.skip_ws();
                if self.peek() == Some(b'}') {
                    self.pos += 1;
                    return Ok(Json::Obj(out));
                }
                loop {
                    self.skip_ws();
                    let key = self.string()?;
                    self.skip_ws();
                    self.expect(b':')?;
                    self.skip_ws();
                    let val = self.value(depth + 1)?;
                    if out.insert(key.clone(), val).is_some() {
                        return Err(self.err(&format!("duplicate object key {key:?}")));
                    }
                    self.skip_ws();
                    match self.peek() {
                        Some(b',') => self.pos += 1,
                        Some(b'}') => {
                            self.pos += 1;
                            return Ok(Json::Obj(out));
                        }
                        _ => return Err(self.err("expected ',' or '}' in object")),
                    }
                }
            }
            Some(b) if b == b'-' || b.is_ascii_digit() => self.number(),
            Some(_) => Err(self.err("unexpected byte at the start of a value")),
        }
    }

    fn number(&mut self) -> Result<Json, ParseError> {
        let start = self.pos;
        if self.peek() == Some(b'-') {
            self.pos += 1;
        }
        while matches!(self.peek(), Some(b) if b.is_ascii_digit()) {
            self.pos += 1;
        }
        if self.peek() == Some(b'.') {
            self.pos += 1;
            while matches!(self.peek(), Some(b) if b.is_ascii_digit()) {
                self.pos += 1;
            }
        }
        if matches!(self.peek(), Some(b'e') | Some(b'E')) {
            self.pos += 1;
            if matches!(self.peek(), Some(b'+') | Some(b'-')) {
                self.pos += 1;
            }
            while matches!(self.peek(), Some(b) if b.is_ascii_digit()) {
                self.pos += 1;
            }
        }
        if self.pos == start {
            return Err(self.err("empty number"));
        }
        let text = std::str::from_utf8(&self.bytes[start..self.pos])
            .map_err(|_| self.err("number is not valid utf-8"))?;
        Ok(Json::Num(text.to_string()))
    }

    fn string(&mut self) -> Result<String, ParseError> {
        self.expect(b'"')?;
        let mut out = String::new();
        loop {
            let b = match self.peek() {
                Some(b) => b,
                None => return Err(self.err("unterminated string")),
            };
            match b {
                b'"' => {
                    self.pos += 1;
                    return Ok(out);
                }
                b'\\' => {
                    self.pos += 1;
                    let e = self.peek().ok_or_else(|| self.err("dangling escape"))?;
                    self.pos += 1;
                    match e {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{8}'),
                        b'f' => out.push('\u{c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let hi = self.hex4()?;
                            let ch = if (0xD800..0xDC00).contains(&hi) {
                                // High surrogate: a low surrogate must follow.
                                self.expect(b'\\')?;
                                self.expect(b'u')?;
                                let lo = self.hex4()?;
                                if !(0xDC00..0xE000).contains(&lo) {
                                    return Err(self.err("expected a low surrogate"));
                                }
                                let cp = 0x10000
                                    + ((hi as u32 - 0xD800) << 10)
                                    + (lo as u32 - 0xDC00);
                                char::from_u32(cp)
                                    .ok_or_else(|| self.err("invalid surrogate pair"))?
                            } else {
                                char::from_u32(hi as u32)
                                    .ok_or_else(|| self.err("invalid \\u escape"))?
                            };
                            out.push(ch);
                        }
                        _ => return Err(self.err("unknown escape")),
                    }
                }
                0x00..=0x1F => return Err(self.err("raw control byte in string")),
                _ => {
                    // Copy one whole UTF-8 scalar.
                    let rest = std::str::from_utf8(&self.bytes[self.pos..])
                        .map_err(|_| self.err("string is not valid utf-8"))?;
                    let ch = rest.chars().next().expect("non-empty by construction");
                    out.push(ch);
                    self.pos += ch.len_utf8();
                }
            }
        }
    }

    fn hex4(&mut self) -> Result<u16, ParseError> {
        if self.pos + 4 > self.bytes.len() {
            return Err(self.err("truncated \\u escape"));
        }
        let s = std::str::from_utf8(&self.bytes[self.pos..self.pos + 4])
            .map_err(|_| self.err("bad \\u escape"))?;
        let v = u16::from_str_radix(s, 16).map_err(|_| self.err("bad \\u escape"))?;
        self.pos += 4;
        Ok(v)
    }
}
