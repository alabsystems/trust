//! Strict duplicate-rejecting JSON and the existing Python ASCII wire encoding.

use crate::value::{Number, Object, Value};

mod printable;

#[derive(Debug)]
pub(crate) struct Error(String);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// The most containers a receipt nests, a rule of this reader and of
/// scripts/lib/stage_receipt_provenance.py (MAX_JSON_NESTING), which words a deeper
/// one the same; neither leaves it to an interpreter's recursion limit. Independent of
/// serde's 128-level container decoder. Parsing and refused-tree cleanup use explicit
/// stacks.
const MAX_NESTING: usize = 1000;

/// The original reader's Python 3.13 default decimal-integer conversion bound, which
/// scripts/lib/stage_receipt_provenance.py holds itself to as well
/// (MAX_JSON_INTEGER_DIGITS) whatever the interpreter's setting. Floating tokens have a
/// separate grammar and are not subject to this limit.
const MAX_INTEGER_DIGITS: usize = 4300;

#[derive(Clone, Copy)]
enum ArrayState {
    FirstOrEnd,
    Value,
    AfterValue,
}
#[derive(Clone, Copy)]
enum ObjectState {
    FirstKeyOrEnd,
    Key,
    Colon,
    Value,
    AfterValue,
}

enum Frame {
    Array { values: Vec<Value>, state: ArrayState },
    Object { values: Object, key: Option<String>, state: ObjectState },
}

impl Frame {
    fn into_value(self) -> Value {
        match self {
            Self::Array { values, .. } => Value::Array(values),
            Self::Object { values, .. } => Value::Object(values),
        }
    }
}

#[derive(Clone, Copy)]
enum Step {
    Value,
    ArrayFirst,
    ObjectFirst,
    ObjectKey,
    Colon,
    ArraySeparator,
    ObjectSeparator,
    End,
}

struct Parser<'a> {
    input: &'a [u8],
    offset: usize,
    frames: Vec<Frame>,
    ready: Option<Value>,
    root: Option<Value>,
}

fn discard(value: Value) {
    // Native Value also cleans accepted trees without recursion.
    drop(value);
}

impl Drop for Parser<'_> {
    fn drop(&mut self) {
        // An error can leave a complete deep subtree in any unfinished frame.
        // Never unwind those Value trees recursively on the caller's stack.
        if let Some(value) = self.ready.take() {
            discard(value);
        }
        if let Some(value) = self.root.take() {
            discard(value);
        }
        while let Some(frame) = self.frames.pop() {
            discard(frame.into_value());
        }
    }
}

impl Parser<'_> {
    fn error(&self, message: &str) -> Error {
        Error(format!("{message} at byte {}", self.offset))
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.offset).copied()
    }

    fn whitespace(&mut self) {
        while self.peek().is_some_and(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n')) {
            self.offset += 1;
        }
    }

    fn consume(&mut self, expected: u8) -> bool {
        if self.peek() == Some(expected) {
            self.offset += 1;
            true
        } else {
            false
        }
    }

    fn string(&mut self) -> Result<String, Error> {
        let start = self.offset;
        if !self.consume(b'"') {
            return Err(self.error("expected a quoted object key"));
        }
        while let Some(byte) = self.peek() {
            self.offset += 1;
            match byte {
                b'"' => {
                    // Only an actual lexical string token enters trust-json.
                    // Receipt objects and number tokens use our lossless model.
                    return match trust_json::from_slice(&self.input[start..self.offset]) {
                        Ok(trust_json::Value::String(value)) => Ok(value),
                        Ok(_) => Err(self.error("quoted token was not a string")),
                        Err(error) => Err(self.error(&error.to_string())),
                    };
                }
                b'\\' => {
                    let escaped =
                        self.peek().ok_or_else(|| self.error("incomplete string escape"))?;
                    self.offset += 1;
                    match escaped {
                        b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => {}
                        b'u' => {
                            for _ in 0..4 {
                                if !self.peek().is_some_and(|b| b.is_ascii_hexdigit()) {
                                    return Err(self.error("incomplete or invalid Unicode escape"));
                                }
                                self.offset += 1;
                            }
                        }
                        _ => return Err(self.error("invalid string escape")),
                    }
                }
                0..=0x1f => return Err(self.error("unescaped control in string")),
                _ => {}
            }
        }
        Err(self.error("unterminated string"))
    }

    fn number(&mut self) -> Result<Number, Error> {
        let start = self.offset;
        self.consume(b'-');
        match self.peek() {
            Some(b'0') => {
                self.offset += 1;
                if self.peek().is_some_and(|b| b.is_ascii_digit()) {
                    return Err(self.error("leading zero in number"));
                }
            }
            Some(b'1'..=b'9') => {
                while self.peek().is_some_and(|b| b.is_ascii_digit()) {
                    self.offset += 1;
                }
            }
            _ => return Err(self.error("number has no integer digits")),
        }
        if self.consume(b'.') {
            let fraction = self.offset;
            while self.peek().is_some_and(|b| b.is_ascii_digit()) {
                self.offset += 1;
            }
            if self.offset == fraction {
                return Err(self.error("number has no fractional digits"));
            }
        }
        if self.peek().is_some_and(|b| matches!(b, b'e' | b'E')) {
            self.offset += 1;
            if self.peek().is_some_and(|b| matches!(b, b'+' | b'-')) {
                self.offset += 1;
            }
            let exponent = self.offset;
            while self.peek().is_some_and(|b| b.is_ascii_digit()) {
                self.offset += 1;
            }
            if self.offset == exponent {
                return Err(self.error("number has no exponent digits"));
            }
        }
        let token = std::str::from_utf8(&self.input[start..self.offset])
            .map_err(|_| self.error("non-ASCII number token"))?;
        if !token.bytes().any(|b| matches!(b, b'.' | b'e' | b'E'))
            && token.strip_prefix('-').unwrap_or(token).len() > MAX_INTEGER_DIGITS
        {
            return Err(self.error("decimal integer exceeds the original 4300-digit limit"));
        }
        Ok(Number::from_validated_token(token))
    }

    fn value(&mut self) -> Result<(), Error> {
        match self.peek() {
            Some(b'[' | b'{') => {
                if self.frames.len() >= MAX_NESTING {
                    return Err(self.error("JSON nesting exceeds 1000 containers"));
                }
                let opening = self.peek().unwrap();
                self.offset += 1;
                self.frames.push(if opening == b'[' {
                    Frame::Array { values: Vec::new(), state: ArrayState::FirstOrEnd }
                } else {
                    Frame::Object {
                        values: Object::new(),
                        key: None,
                        state: ObjectState::FirstKeyOrEnd,
                    }
                });
            }
            Some(b'"') => self.ready = Some(Value::String(self.string()?)),
            Some(b'-' | b'0'..=b'9') => self.ready = Some(Value::Number(self.number()?)),
            Some(b't' | b'f' | b'n') => {
                let (literal, value): (&[u8], Value) = match self.peek().unwrap() {
                    b't' => (b"true", Value::Bool(true)),
                    b'f' => (b"false", Value::Bool(false)),
                    _ => (b"null", Value::Null),
                };
                if !self.input[self.offset..].starts_with(literal) {
                    return Err(self.error("invalid JSON literal"));
                }
                self.offset += literal.len();
                self.ready = Some(value);
            }
            _ => return Err(self.error("expected a JSON value")),
        }
        Ok(())
    }

    fn key(&mut self) -> Result<(), Error> {
        let key = self.string()?;
        if let Some(Frame::Object { values, key: pending, state }) = self.frames.last_mut() {
            if values.contains_key(&key) {
                return Err(self.error(&format!("it repeats the key {key:?}")));
            }
            *pending = Some(key);
            *state = ObjectState::Colon;
            Ok(())
        } else {
            Err(self.error("object key outside an object"))
        }
    }

    fn close(&mut self) {
        self.offset += 1;
        self.ready = Some(self.frames.pop().expect("closing an existing frame").into_value());
    }

    fn run(&mut self) -> Result<Value, Error> {
        loop {
            if let Some(value) = self.ready.take() {
                match self.frames.last_mut() {
                    Some(Frame::Array { values, state }) => {
                        values.push(value);
                        *state = ArrayState::AfterValue;
                    }
                    Some(Frame::Object { values, key, state }) => {
                        values.insert(key.take().expect("object value follows its key"), value);
                        *state = ObjectState::AfterValue;
                    }
                    None => self.root = Some(value),
                }
                continue;
            }
            self.whitespace();
            let step = match self.frames.last() {
                Some(Frame::Array { state: ArrayState::FirstOrEnd, .. }) => Step::ArrayFirst,
                Some(Frame::Array { state: ArrayState::Value, .. }) => Step::Value,
                Some(Frame::Array { state: ArrayState::AfterValue, .. }) => Step::ArraySeparator,
                Some(Frame::Object { state: ObjectState::FirstKeyOrEnd, .. }) => Step::ObjectFirst,
                Some(Frame::Object { state: ObjectState::Key, .. }) => Step::ObjectKey,
                Some(Frame::Object { state: ObjectState::Colon, .. }) => Step::Colon,
                Some(Frame::Object { state: ObjectState::Value, .. }) => Step::Value,
                Some(Frame::Object { state: ObjectState::AfterValue, .. }) => Step::ObjectSeparator,
                None if self.root.is_some() => Step::End,
                None => Step::Value,
            };
            match step {
                Step::Value => self.value()?,
                Step::ArrayFirst => {
                    if self.peek() == Some(b']') {
                        self.close();
                    } else {
                        self.value()?;
                    }
                }
                Step::ObjectFirst => {
                    if self.peek() == Some(b'}') {
                        self.close();
                    } else {
                        self.key()?;
                    }
                }
                Step::ObjectKey => self.key()?,
                Step::Colon => {
                    if !self.consume(b':') {
                        return Err(self.error("expected colon after object key"));
                    }
                    if let Some(Frame::Object { state, .. }) = self.frames.last_mut() {
                        *state = ObjectState::Value;
                    }
                }
                Step::ArraySeparator => {
                    if self.consume(b',') {
                        if let Some(Frame::Array { state, .. }) = self.frames.last_mut() {
                            *state = ArrayState::Value;
                        }
                    } else if self.peek() == Some(b']') {
                        self.close();
                    } else {
                        return Err(self.error("expected array comma or closing bracket"));
                    }
                }
                Step::ObjectSeparator => {
                    if self.consume(b',') {
                        if let Some(Frame::Object { state, .. }) = self.frames.last_mut() {
                            *state = ObjectState::Key;
                        }
                    } else if self.peek() == Some(b'}') {
                        self.close();
                    } else {
                        return Err(self.error("expected object comma or closing brace"));
                    }
                }
                Step::End => {
                    if self.offset != self.input.len() {
                        return Err(self.error("trailing data after JSON value"));
                    }
                    return Ok(self.root.take().expect("completed root value"));
                }
            }
        }
    }
}

pub(crate) fn parse(bytes: &[u8]) -> Result<Value, Error> {
    if bytes.len() as u64 > crate::MAX_RECEIPT_BYTES {
        return Err(Error("JSON exceeds the 16 MiB receipt bound".into()));
    }
    Parser { input: bytes, offset: 0, frames: Vec::new(), ready: None, root: None }.run()
}

/// Match Python's sorted ensure_ascii wire encoding for the validated LLVM
/// source-row vocabulary (arrays/objects/strings). Numeric metadata retains its
/// lossless JSON representation; numbers are not valid source-row fields.
pub(crate) fn ascii_canonical(value: &Value) -> String {
    encode(value, true)
}

/// Iterative JSON output. Canonical digests sort keys; diagnostic round trips
/// retain the original object order. Neither changes numeric token spelling.
pub(crate) fn encode(value: &Value, sort_keys: bool) -> String {
    fn quoted(text: &str, out: &mut String) {
        use std::fmt::Write as _;
        out.push('"');
        for c in text.chars() {
            match c {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\u{8}' => out.push_str("\\b"),
                '\u{c}' => out.push_str("\\f"),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                c if (' '..='~').contains(&c) => out.push(c),
                c => {
                    let mut units = [0; 2];
                    for unit in c.encode_utf16(&mut units) {
                        write!(out, "\\u{unit:04x}").expect("String writes cannot fail");
                    }
                }
            }
        }
        out.push('"');
    }
    enum Emit<'a> {
        Value(&'a Value),
        Quoted(&'a str),
        Text(&'static str),
    }
    let mut out = String::new();
    let mut pending = vec![Emit::Value(value)];
    while let Some(item) = pending.pop() {
        match item {
            Emit::Text(text) => out.push_str(text),
            Emit::Quoted(text) => quoted(text, &mut out),
            Emit::Value(value) => match value {
                Value::Null => out.push_str("null"),
                Value::Bool(value) => out.push_str(if *value { "true" } else { "false" }),
                Value::Number(value) => out.push_str(value.as_str()),
                Value::String(value) => quoted(value, &mut out),
                Value::Array(values) => {
                    out.push('[');
                    pending.push(Emit::Text("]"));
                    for (i, value) in values.iter().enumerate().rev() {
                        pending.push(Emit::Value(value));
                        if i > 0 {
                            pending.push(Emit::Text(","));
                        }
                    }
                }
                Value::Object(values) => {
                    let mut entries = values.iter().collect::<Vec<_>>();
                    if sort_keys {
                        entries.sort_by(|a, b| a.0.cmp(b.0));
                    }
                    out.push('{');
                    pending.push(Emit::Text("}"));
                    for (i, (key, value)) in entries.into_iter().enumerate().rev() {
                        pending.push(Emit::Value(value));
                        pending.push(Emit::Text(":"));
                        pending.push(Emit::Quoted(key));
                        if i > 0 {
                            pending.push(Emit::Text(","));
                        }
                    }
                }
            },
        }
    }
    out
}

/// Python-compatible diagnostics do not participate in receipt identity.
/// Integer tokens are never narrowed. Only an explicitly floating lexical
/// token is interpreted as a Python binary float for its diagnostic repr;
/// the native value always retains that token byte for byte.
pub(crate) fn python_repr(value: &Value) -> String {
    fn quoted(text: &str, out: &mut String) {
        use std::fmt::Write as _;
        let quote = if text.contains('\'') && !text.contains('"') { '"' } else { '\'' };
        out.push(quote);
        for c in text.chars() {
            match c {
                '\\' => out.push_str("\\\\"),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                c if c == quote => {
                    out.push('\\');
                    out.push(c);
                }
                c if printable::is_printable(c) => out.push(c),
                c if (c as u32) <= 0xff => {
                    write!(out, "\\x{:02x}", c as u32).expect("String write");
                }
                c if (c as u32) <= 0xffff => {
                    write!(out, "\\u{:04x}", c as u32).expect("String write");
                }
                c => {
                    write!(out, "\\U{:08x}", c as u32).expect("String write");
                }
            }
        }
        out.push(quote);
    }
    fn number(number: &Number, out: &mut String) {
        use std::fmt::Write as _;
        let token = number.as_str();
        if number.is_integer() {
            out.push_str(if token == "-0" { "0" } else { token });
            return;
        }
        let Ok(value) = token.parse::<f64>() else {
            // Token validity belongs to the lexer, not a binary-float parser.
            // An implementation-specific conversion refusal never narrows or
            // rejects the stored JSON number, and cannot panic diagnostics.
            out.push_str(token);
            return;
        };
        if value.is_infinite() {
            out.push_str(if value.is_sign_negative() { "-inf" } else { "inf" });
            return;
        }
        let mut buffer = trust_json::ser::float::FloatBuffer::new();
        let text = buffer.format_finite_f64(value);
        if let Some((mantissa, exponent)) = text.split_once('e') {
            let exponent: i32 = exponent.parse().expect("native float exponent");
            write!(out, "{mantissa}e{exponent:+03}").expect("String write");
        } else {
            // The native JSON writer uses fixed notation at exponent -5;
            // Python switches to scientific notation below exponent -4.
            let (sign, magnitude) = text.strip_prefix('-').map_or(("", text), |v| ("-", v));
            if let Some(digits) =
                magnitude.strip_prefix("0.0000").filter(|s| !s.is_empty() && !s.starts_with('0'))
            {
                out.push_str(sign);
                out.push_str(&digits[..1]);
                if digits.len() > 1 {
                    out.push('.');
                    out.push_str(&digits[1..]);
                }
                out.push_str("e-05");
                return;
            }
            out.push_str(text);
        }
    }
    enum Emit<'a> {
        Value(&'a Value),
        Quoted(&'a str),
        Text(&'static str),
    }
    let mut out = String::new();
    let mut pending = vec![Emit::Value(value)];
    while let Some(step) = pending.pop() {
        match step {
            Emit::Quoted(text) => quoted(text, &mut out),
            Emit::Text(text) => out.push_str(text),
            Emit::Value(value) => match value {
                Value::Null => out.push_str("None"),
                Value::Bool(value) => out.push_str(if *value { "True" } else { "False" }),
                Value::Number(value) => number(value, &mut out),
                Value::String(value) => quoted(value, &mut out),
                Value::Array(values) => {
                    out.push('[');
                    pending.push(Emit::Text("]"));
                    for (i, value) in values.iter().enumerate().rev() {
                        pending.push(Emit::Value(value));
                        if i > 0 {
                            pending.push(Emit::Text(", "));
                        }
                    }
                }
                Value::Object(values) => {
                    out.push('{');
                    pending.push(Emit::Text("}"));
                    for (i, (key, value)) in values.iter().enumerate().rev() {
                        pending.push(Emit::Value(value));
                        pending.push(Emit::Text(": "));
                        pending.push(Emit::Quoted(key));
                        if i > 0 {
                            pending.push(Emit::Text(", "));
                        }
                    }
                }
            },
        }
    }
    out
}

#[cfg(test)]
mod tests;
