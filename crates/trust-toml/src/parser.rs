// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A recursive-descent reader for TOML v1.0.0.
//!
//! # What "correct" means here, and why it is not "it parsed"
//!
//! A configuration reader has an unusually nasty failure mode: it does not
//! crash on a document it misunderstands, it returns a *different
//! configuration*. `a.b = 1` read as a flat key `"a.b"` produces a perfectly
//! good value that no consumer will ever find, and the consumer's
//! `#[serde(default)]` then supplies a plausible substitute. Nothing is red.
//! That is why the acceptance gate for this crate is a differential against the
//! incumbent over the repository's own 1360-file TOML corpus rather than a
//! hand-written suite: hand-written tests can only cover the constructs the
//! author remembered, and the constructs an author forgets are exactly the ones
//! that fail silently.
//!
//! The grammar constructs measured to be present in that corpus are, in
//! descending frequency: inline tables (464 files), dotted keys (148), arrays
//! of tables (127), multi-line arrays (124), literal strings (18), multi-line
//! basic strings (14), quoted keys (11), escape sequences (8), hex/octal/binary
//! integers (3), multi-line literal strings (3), floats (1). Zero datetimes,
//! zero exponent floats, zero `inf`/`nan`, zero underscored integers. Every one
//! of those is implemented, and so is everything measured *absent* — a reader
//! that only handles what today's corpus contains is a trap for tomorrow's
//! corpus.
//!
//! # The part that is easy to get subtly wrong: table identity
//!
//! TOML's hard rules are not about tokens, they are about which table a key
//! lands in and whether a table may be opened twice. A parser that merges
//! silently instead of rejecting will read
//!
//! ```toml
//! [server]
//! port = 1
//! [server]
//! port = 2
//! ```
//!
//! as `port = 2` — a last-one-wins misconfiguration that TOML requires to be an
//! error. This module therefore does not build a plain map. It builds a tree of
//! [`TableBuilder`]s that remembers **how** each table came into existence
//! ([`TableKind`]), because the legality of an operation depends on that
//! history and on nothing else:
//!
//! * a table made implicitly by a header path (`a` in `[a.b]`) may later be
//!   opened explicitly by `[a]`;
//! * a table made explicitly may not be opened again;
//! * a table made by a dotted key (`a` in `a.b = 1`) may not be opened by a
//!   header at all, but sub-tables *may* be added beneath it — TOML v1.0.0
//!   §Table states exactly this asymmetry;
//! * a value, including an inline table and an array of values, is closed
//!   forever the moment it is written.
//!
//! # Positions are carried on every node
//!
//! Each parsed node keeps the line and column it started at. That is what lets
//! a *deserialization* failure — "invalid type: string, expected an integer" —
//! be reported at the offending value rather than at the top of the file. The
//! extra `usize` pair per node is the price; configuration documents are small
//! and the diagnosis is worth more than the bytes.

use crate::datetime::{self, Datetime};
use crate::error::Error;
use crate::map::Map;

/// A parsed node together with where it started.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Item {
    pub kind: Kind,
    pub line: usize,
    /// 1-based, counted in `char`s.
    pub column: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Kind {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Datetime(Datetime),
    Array(Vec<Item>),
    Table(Map<String, Item>),
}

impl Kind {
    /// The noun used in `invalid type: ...` messages. Deliberately the same
    /// vocabulary serde uses, so a message reads naturally when serde supplies
    /// the "expected" half.
    pub(crate) fn type_name(&self) -> &'static str {
        match self {
            Self::String(_) => "string",
            Self::Integer(_) => "integer",
            Self::Float(_) => "float",
            Self::Boolean(_) => "boolean",
            Self::Datetime(_) => "datetime",
            Self::Array(_) => "array",
            Self::Table(_) => "table",
        }
    }
}

/// How a table came to exist. See the module docs — this is the whole reason
/// the builder tree exists rather than a plain map.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TableKind {
    /// The document root, or the body of an inline table.
    Root,
    /// Named directly by a `[header]` or `[[header]]`.
    Explicit,
    /// Brought into being as an ancestor in a header path: `a` in `[a.b]`.
    /// May later be promoted to [`Self::Explicit`] by its own `[a]`.
    ImplicitHeader,
    /// Brought into being by a dotted key: `a` in `a.b = 1`. May never be
    /// opened by a header, but sub-tables may be added under it.
    ImplicitDotted,
}

#[derive(Debug)]
enum Slot {
    /// A written value. Closed: scalars, arrays of values, and inline tables
    /// all land here and none of them may be extended afterwards.
    Value(Item),
    Table(TableBuilder),
    ArrayOfTables {
        items: Vec<TableBuilder>,
        line: usize,
        column: usize,
    },
}

#[derive(Debug)]
struct TableBuilder {
    entries: Map<String, Slot>,
    kind: TableKind,
    line: usize,
    column: usize,
}

impl TableBuilder {
    fn new(kind: TableKind, line: usize, column: usize) -> Self {
        Self { entries: Map::new(), kind, line, column }
    }

    fn finish(self) -> Item {
        let mut table = Map::new();
        for (name, slot) in self.entries {
            let item = match slot {
                Slot::Value(item) => item,
                Slot::Table(builder) => builder.finish(),
                Slot::ArrayOfTables { items, line, column } => Item {
                    kind: Kind::Array(items.into_iter().map(TableBuilder::finish).collect()),
                    line,
                    column,
                },
            };
            table.insert(name, item);
        }
        Item { kind: Kind::Table(table), line: self.line, column: self.column }
    }
}

/// One component of a (possibly dotted) key, with its own position so a
/// duplicate-key error points at the duplicate and not at the line start.
#[derive(Debug, Clone)]
struct KeyPart {
    name: String,
    line: usize,
    column: usize,
}

/// Parse a whole TOML document into the root table.
pub(crate) fn parse_document(source: &str) -> Result<Item, Error> {
    Parser::new(source).document()
}

/// The maximum nesting this parser will descend, and the maximum number of
/// parts in a dotted key path.
///
/// FOUND BY THE ADVERSARIAL DIFFERENTIAL, and it was the worst finding of the
/// run: without it, `a = [[[[…1…]]]]` at depth 5000 **overflowed the stack and
/// aborted the process**. Not a panic — an abort. `catch_unwind` cannot see it,
/// a consumer cannot recover from it, and the input that causes it is an
/// eleven-kilobyte file. `targo` reads `Cargo.toml` files it did not write, so
/// "the caller controls the input" is not true here.
///
/// Measured on this clone, `cargo test` default stack: arrays aborted between
/// depth 1000 and 5000, inline tables and dotted key paths between 100 and
/// 1000. The exact threshold is a function of stack size and build profile,
/// which is precisely why a *measured* threshold is not a fix and a *declared*
/// one is.
///
/// The number is 80 because that is the incumbent's, at
/// `toml_edit-0.22.27/src/parser/mod.rs:97` — `const LIMIT: usize = 80` — and
/// matching it exactly is what keeps the two implementations agreeing on
/// accept/reject rather than merely both refusing eventually. The incumbent's
/// comparison is `LIMIT <= current` **after** incrementing, so 79 levels are
/// accepted and the 80th is refused; `tests/adversarial.rs` pins both sides of
/// that boundary against the incumbent rather than against this comment.
const MAX_DEPTH: usize = 80;

struct Parser<'a> {
    source: &'a str,
    pos: usize,
    line: usize,
    line_start: usize,
    /// Nesting depth of the value currently being parsed: arrays and inline
    /// tables share one counter, as they do in the incumbent (`check_recursion`
    /// wraps both `array` and `inline_table` at `src/parser/value.rs:25-26`).
    depth: usize,
}

impl<'a> Parser<'a> {
    fn new(source: &'a str) -> Self {
        // A single leading UTF-8 byte-order mark is consumed, not rejected.
        //
        // FOUND BY THE ADVERSARIAL DIFFERENTIAL. Before this, `\u{FEFF}a = 1`
        // was a hard parse error here and an accepted document for the
        // incumbent, which strips it at `toml_edit-0.22.27`,
        // `src/parser/document.rs:36` — `opt(b"\xEF\xBB\xBF")`, the first thing
        // its document parser does. Windows editors write that mark by default,
        // so a dependency rename would have turned every BOM-prefixed
        // configuration file in the fleet into a build error. The corpus cannot
        // see this: no file in it carries a BOM.
        //
        // `opt` is exactly once, and the differential pins the consequences of
        // that: TWO marks stay an error (the second is not a key), and a mark
        // anywhere but offset 0 stays an error. `pos` starts past the mark
        // rather than the source being re-sliced, so every byte offset this
        // parser reports still indexes the caller's own string.
        let pos = if source.starts_with('\u{FEFF}') { '\u{FEFF}'.len_utf8() } else { 0 };
        Self { source, pos, line: 1, line_start: 0, depth: 0 }
    }

    /// Run `body` one level deeper, refusing at [`MAX_DEPTH`].
    ///
    /// The counter is decremented on the way out, so depth is nesting and not a
    /// running total — `a = [1]` a thousand times over is fine, and
    /// `a = [[[…]]]` a thousand deep is not. Matching the incumbent's
    /// enter/exit pair rather than a high-water mark is what makes the two
    /// agree on a document like `[[a], [[b]], [[[c]]]]`.
    fn nested<T>(&mut self, body: impl FnOnce(&mut Self) -> Result<T, Error>) -> Result<T, Error> {
        self.depth += 1;
        if self.depth >= MAX_DEPTH {
            // Reported at the current position, not at the opening bracket:
            // the offending construct is the one that crossed the line.
            return Err(self.error("nesting is too deep"));
        }
        let result = body(self);
        self.depth -= 1;
        result
    }

    // -- cursor ------------------------------------------------------------

    fn eof(&self) -> bool {
        self.pos >= self.source.len()
    }

    /// The next byte. Safe for ASCII comparisons: in UTF-8 a byte below 0x80
    /// occurs only as a whole ASCII character, never inside a multi-byte one.
    fn peek(&self) -> Option<u8> {
        self.source.as_bytes().get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.source.as_bytes().get(self.pos + offset).copied()
    }

    /// Advance one whole `char`, keeping the line counter honest.
    ///
    /// Always advancing by `len_utf8` is what keeps `self.pos` on a character
    /// boundary, which in turn is what makes [`Self::column`]'s slice-and-count
    /// safe and makes every `&self.source[start..self.pos]` slice legal.
    fn bump(&mut self) -> Option<char> {
        let next = self.source[self.pos..].chars().next()?;
        self.pos += next.len_utf8();
        if next == '\n' {
            self.line += 1;
            self.line_start = self.pos;
        }
        Some(next)
    }

    fn eat(&mut self, byte: u8) -> bool {
        if self.peek() == Some(byte) {
            self.bump();
            true
        } else {
            false
        }
    }

    /// 1-based column, in characters.
    fn column(&self) -> usize {
        self.source[self.line_start..self.pos].chars().count() + 1
    }

    fn here(&self) -> (usize, usize) {
        (self.line, self.column())
    }

    fn error(&self, message: impl Into<String>) -> Error {
        Error::at(message, self.line, self.column())
    }

    fn expect(&mut self, byte: u8, context: &str) -> Result<(), Error> {
        if self.eat(byte) {
            Ok(())
        } else {
            let found = match self.peek() {
                None => "end of input".to_string(),
                Some(_) => format!("`{}`", self.source[self.pos..].chars().next().unwrap()),
            };
            Err(self.error(format!("expected `{}` {context}, found {found}", byte as char)))
        }
    }

    // -- trivia ------------------------------------------------------------

    /// Spaces and tabs only. Never newlines: in TOML a newline is a statement
    /// terminator, so skipping it here would silently accept `a =\n1`.
    fn skip_ws(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t')) {
            self.bump();
        }
    }

    /// A `#` comment, up to but not including the newline.
    fn skip_comment(&mut self) -> Result<(), Error> {
        debug_assert_eq!(self.peek(), Some(b'#'));
        self.bump();
        while let Some(byte) = self.peek() {
            if byte == b'\n' {
                break;
            }
            let (line, column) = self.here();
            let next = self.bump().expect("peeked");
            // TOML v1.0.0: "Control characters other than tab are not permitted
            // in comments." Enforced rather than ignored — a stray control byte
            // in a config file is a corrupted file, and reading it as if it were
            // fine is the failure mode this crate exists to remove.
            if is_forbidden_control(next) {
                return Err(Error::at(
                    format!(
                        "control character U+{:04X} is not permitted in a comment",
                        next as u32
                    ),
                    line,
                    column,
                ));
            }
        }
        Ok(())
    }

    /// Consume one newline. `\r` is only legal as part of `\r\n`.
    fn newline(&mut self) -> Result<(), Error> {
        if self.eat(b'\n') {
            return Ok(());
        }
        if self.peek() == Some(b'\r') {
            if self.peek_at(1) == Some(b'\n') {
                self.bump();
                self.bump();
                return Ok(());
            }
            return Err(self.error("a bare carriage return is not a TOML newline; use `\\r\\n`"));
        }
        Err(self.error("expected a newline"))
    }

    /// Whitespace, comments and newlines, between statements.
    fn skip_trivia(&mut self) -> Result<(), Error> {
        loop {
            self.skip_ws();
            match self.peek() {
                Some(b'#') => self.skip_comment()?,
                Some(b'\n') | Some(b'\r') => self.newline()?,
                _ => return Ok(()),
            }
        }
    }

    /// After a statement: optional trailing whitespace and comment, then the
    /// line must end. Without this, `a = 1 b = 2` would parse as `a = 1`
    /// followed by a second statement — accepting a document TOML rejects.
    fn finish_line(&mut self) -> Result<(), Error> {
        self.skip_ws();
        if self.peek() == Some(b'#') {
            self.skip_comment()?;
        }
        if self.eof() {
            return Ok(());
        }
        self.newline()
            .map_err(|_| self.error("expected a newline or end of input after this statement"))
    }

    // -- document ----------------------------------------------------------

    fn document(mut self) -> Result<Item, Error> {
        let mut root = TableBuilder::new(TableKind::Root, 1, 1);
        // The active table, as a path from the root. Stored as a path rather
        // than as a `&mut TableBuilder` so that a header can rewrite it without
        // fighting the borrow checker; documents are shallow and re-descending
        // costs nothing measurable.
        let mut current: Vec<String> = Vec::new();

        loop {
            self.skip_trivia()?;
            if self.eof() {
                break;
            }
            if self.peek() == Some(b'[') {
                current = self.table_header(&mut root)?;
            } else {
                let keys = self.parse_key_path()?;
                self.skip_ws();
                self.expect(b'=', "after a key")?;
                self.skip_ws();
                let value = self.parse_value()?;
                let table = resolve_current(&mut root, &current);
                insert_dotted(table, &keys, value)?;
                self.finish_line()?;
            }
        }
        Ok(root.finish())
    }

    /// `[a.b]` or `[[a.b]]`. Returns the new active table path.
    fn table_header(&mut self, root: &mut TableBuilder) -> Result<Vec<String>, Error> {
        let (line, column) = self.here();
        self.expect(b'[', "to open a table header")?;
        let array = self.eat(b'[');
        self.skip_ws();
        let keys = self.parse_key_path()?;
        self.skip_ws();
        self.expect(b']', "to close a table header")?;
        if array {
            self.expect(b']', "to close an array-of-tables header")?;
        }
        self.finish_line()?;

        let (last, ancestors) = keys.split_last().expect("a key path has at least one part");
        let mut cursor = root;
        for part in ancestors {
            cursor = descend_header(cursor, part)?;
        }

        if array {
            open_array_of_tables(cursor, last, line, column)?;
        } else {
            open_table(cursor, last, line, column)?;
        }
        Ok(keys.into_iter().map(|part| part.name).collect())
    }

    // -- keys --------------------------------------------------------------

    fn parse_key_path(&mut self) -> Result<Vec<KeyPart>, Error> {
        let mut parts = vec![self.parse_key_part()?];
        loop {
            self.skip_ws();
            if self.peek() == Some(b'.') {
                self.bump();
                self.skip_ws();
                parts.push(self.parse_key_part()?);
            } else {
                // The incumbent checks the whole path once it is collected
                // (`toml_edit-0.22.27/src/parser/key.rs:38`,
                // `RecursionCheck::check_depth(k.len())`) with the same `LIMIT
                // <= depth` comparison, because inserting a 5000-part dotted
                // key recurses through 5000 nested tables on the way in. It is
                // the same abort with a different shape, and it is checked here
                // rather than at the insert so that a header and a key-value
                // line get the identical rule from one place.
                if parts.len() >= MAX_DEPTH {
                    return Err(self.error("the dotted key path is too deep"));
                }
                return Ok(parts);
            }
        }
    }

    fn parse_key_part(&mut self) -> Result<KeyPart, Error> {
        let (line, column) = self.here();
        let name = match self.peek() {
            Some(b'"') => self.parse_basic_string(false)?,
            Some(b'\'') => self.parse_literal_string(false)?,
            Some(byte) if is_bare_key_byte(byte) => {
                let start = self.pos;
                while matches!(self.peek(), Some(byte) if is_bare_key_byte(byte)) {
                    self.bump();
                }
                self.source[start..self.pos].to_string()
            }
            _ => return Err(self.error("expected a key")),
        };
        Ok(KeyPart { name, line, column })
    }

    // -- values ------------------------------------------------------------

    fn parse_value(&mut self) -> Result<Item, Error> {
        let (line, column) = self.here();
        let kind = match self.peek() {
            None => return Err(self.error("expected a value")),
            Some(b'"') => {
                if self.peek_at(1) == Some(b'"') && self.peek_at(2) == Some(b'"') {
                    Kind::String(self.parse_basic_string(true)?)
                } else {
                    Kind::String(self.parse_basic_string(false)?)
                }
            }
            Some(b'\'') => {
                if self.peek_at(1) == Some(b'\'') && self.peek_at(2) == Some(b'\'') {
                    Kind::String(self.parse_literal_string(true)?)
                } else {
                    Kind::String(self.parse_literal_string(false)?)
                }
            }
            Some(b'[') => Kind::Array(self.nested(Self::parse_array)?),
            Some(b'{') => Kind::Table(self.nested(Self::parse_inline_table)?),
            Some(b't') if self.starts_with("true") => {
                self.advance_bytes(4);
                Kind::Boolean(true)
            }
            Some(b'f') if self.starts_with("false") => {
                self.advance_bytes(5);
                Kind::Boolean(false)
            }
            Some(_) => self.parse_number_or_datetime()?,
        };
        Ok(Item { kind, line, column })
    }

    fn starts_with(&self, text: &str) -> bool {
        self.source[self.pos..].starts_with(text)
    }

    /// Advance over a run of bytes already known to be ASCII (a keyword).
    fn advance_bytes(&mut self, count: usize) {
        for _ in 0..count {
            self.bump();
        }
    }

    fn parse_array(&mut self) -> Result<Vec<Item>, Error> {
        self.expect(b'[', "to open an array")?;
        let mut items = Vec::new();
        loop {
            // Arrays may span lines and carry comments anywhere inside.
            self.skip_trivia()?;
            if self.eat(b']') {
                return Ok(items);
            }
            items.push(self.parse_value()?);
            self.skip_trivia()?;
            if self.eat(b',') {
                continue;
            }
            self.skip_trivia()?;
            if self.eat(b']') {
                return Ok(items);
            }
            return Err(self.error("expected `,` or `]` in an array"));
        }
    }

    fn parse_inline_table(&mut self) -> Result<Map<String, Item>, Error> {
        let (line, column) = self.here();
        self.expect(b'{', "to open an inline table")?;
        let mut builder = TableBuilder::new(TableKind::Root, line, column);
        self.skip_ws();
        if self.eat(b'}') {
            return Ok(finish_inline(builder));
        }
        loop {
            // Deliberately `skip_ws`, not `skip_trivia`: TOML v1.0.0 forbids
            // newlines inside an inline table. Accepting them would silently
            // read a document the incumbent rejects.
            self.skip_ws();
            let keys = self.parse_key_path()?;
            self.skip_ws();
            self.expect(b'=', "after a key in an inline table")?;
            self.skip_ws();
            let value = self.parse_value()?;
            insert_dotted(&mut builder, &keys, value)?;
            self.skip_ws();
            if self.eat(b',') {
                self.skip_ws();
                if self.peek() == Some(b'}') {
                    // TOML v1.0.0 forbids a trailing comma in an inline table
                    // (unlike an array, which allows one).
                    return Err(self.error("a trailing comma is not allowed in an inline table"));
                }
                continue;
            }
            self.skip_ws();
            if self.eat(b'}') {
                return Ok(finish_inline(builder));
            }
            return Err(self.error("expected `,` or `}` in an inline table"));
        }
    }

    // -- strings -----------------------------------------------------------

    fn parse_basic_string(&mut self, multiline: bool) -> Result<String, Error> {
        let (open_line, open_column) = self.here();
        let delimiter = if multiline { 3 } else { 1 };
        for _ in 0..delimiter {
            self.expect(b'"', "to open a string")?;
        }
        if multiline {
            self.trim_leading_newline();
        }

        let mut out = String::new();
        loop {
            let Some(byte) = self.peek() else {
                return Err(Error::at("unterminated string", open_line, open_column));
            };
            if byte == b'"' {
                if !multiline {
                    self.bump();
                    return Ok(out);
                }
                let quotes = self.count_run(b'"');
                if quotes < 3 {
                    for _ in 0..quotes {
                        self.bump();
                        out.push('"');
                    }
                    continue;
                }
                if quotes > 5 {
                    return Err(self.error(
                        "more than five consecutive `\"` cannot appear in a multi-line string",
                    ));
                }
                // Three quotes close the string; a fourth and fifth belong to
                // its content, which is how `""""` denotes a string holding one
                // quote character.
                for _ in 0..quotes - 3 {
                    out.push('"');
                }
                self.advance_bytes(quotes);
                return Ok(out);
            }
            if byte == b'\\' {
                self.bump();
                if multiline && self.at_line_ending_backslash() {
                    self.skip_line_ending_backslash()?;
                    continue;
                }
                out.push(self.parse_escape()?);
                continue;
            }
            if byte == b'\n' || byte == b'\r' {
                if !multiline {
                    return Err(self.error("a newline is not allowed in a single-line string"));
                }
                self.newline()?;
                out.push('\n');
                continue;
            }
            let (line, column) = self.here();
            let next = self.bump().expect("peeked");
            if is_forbidden_control(next) {
                return Err(Error::at(
                    format!("control character U+{:04X} is not permitted in a string", next as u32),
                    line,
                    column,
                ));
            }
            out.push(next);
        }
    }

    fn parse_literal_string(&mut self, multiline: bool) -> Result<String, Error> {
        let (open_line, open_column) = self.here();
        let delimiter = if multiline { 3 } else { 1 };
        for _ in 0..delimiter {
            self.expect(b'\'', "to open a literal string")?;
        }
        if multiline {
            self.trim_leading_newline();
        }

        let mut out = String::new();
        loop {
            let Some(byte) = self.peek() else {
                return Err(Error::at("unterminated literal string", open_line, open_column));
            };
            if byte == b'\'' {
                if !multiline {
                    self.bump();
                    return Ok(out);
                }
                let quotes = self.count_run(b'\'');
                if quotes < 3 {
                    for _ in 0..quotes {
                        self.bump();
                        out.push('\'');
                    }
                    continue;
                }
                if quotes > 5 {
                    return Err(self.error(
                        "more than five consecutive `'` cannot appear in a multi-line literal string",
                    ));
                }
                for _ in 0..quotes - 3 {
                    out.push('\'');
                }
                self.advance_bytes(quotes);
                return Ok(out);
            }
            if byte == b'\n' || byte == b'\r' {
                if !multiline {
                    return Err(
                        self.error("a newline is not allowed in a single-line literal string")
                    );
                }
                self.newline()?;
                out.push('\n');
                continue;
            }
            let (line, column) = self.here();
            let next = self.bump().expect("peeked");
            if is_forbidden_control(next) {
                return Err(Error::at(
                    format!(
                        "control character U+{:04X} is not permitted in a literal string",
                        next as u32
                    ),
                    line,
                    column,
                ));
            }
            out.push(next);
        }
    }

    /// A newline immediately after `"""` / `'''` is not part of the content.
    fn trim_leading_newline(&mut self) {
        if self.peek() == Some(b'\n') {
            self.bump();
        } else if self.peek() == Some(b'\r') && self.peek_at(1) == Some(b'\n') {
            self.bump();
            self.bump();
        }
    }

    fn count_run(&self, byte: u8) -> usize {
        let mut count = 0;
        while self.peek_at(count) == Some(byte) {
            count += 1;
        }
        count
    }

    /// A `\` at the end of a line (possibly with trailing spaces) in a
    /// multi-line basic string swallows the newline and the following
    /// indentation.
    fn at_line_ending_backslash(&self) -> bool {
        let mut offset = 0;
        while matches!(self.peek_at(offset), Some(b' ' | b'\t')) {
            offset += 1;
        }
        matches!(self.peek_at(offset), Some(b'\n') | Some(b'\r'))
    }

    fn skip_line_ending_backslash(&mut self) -> Result<(), Error> {
        loop {
            match self.peek() {
                Some(b' ' | b'\t') => {
                    self.bump();
                }
                Some(b'\n') | Some(b'\r') => self.newline()?,
                _ => return Ok(()),
            }
        }
    }

    fn parse_escape(&mut self) -> Result<char, Error> {
        let (line, column) = self.here();
        let Some(escape) = self.bump() else {
            return Err(Error::at("unterminated escape sequence", line, column));
        };
        Ok(match escape {
            'b' => '\u{8}',
            't' => '\t',
            'n' => '\n',
            'f' => '\u{c}',
            'r' => '\r',
            '"' => '"',
            '\\' => '\\',
            'u' => self.parse_unicode_escape(4, line, column)?,
            'U' => self.parse_unicode_escape(8, line, column)?,
            // No `\e`, no `\x`: those are TOML v1.1 proposals. Accepting them
            // would read documents the incumbent rejects.
            other => {
                return Err(Error::at(
                    format!("unknown escape sequence `\\{other}`"),
                    line,
                    column,
                ));
            }
        })
    }

    fn parse_unicode_escape(
        &mut self,
        digits: usize,
        line: usize,
        column: usize,
    ) -> Result<char, Error> {
        let start = self.pos;
        for _ in 0..digits {
            match self.peek() {
                Some(byte) if byte.is_ascii_hexdigit() => {
                    self.bump();
                }
                _ => {
                    return Err(Error::at(
                        format!(
                            "a `\\{}` escape needs exactly {digits} hex digits",
                            if digits == 4 { 'u' } else { 'U' }
                        ),
                        line,
                        column,
                    ));
                }
            }
        }
        let scalar = u32::from_str_radix(&self.source[start..self.pos], 16)
            .map_err(|_| Error::at("invalid unicode escape", line, column))?;
        char::from_u32(scalar).ok_or_else(|| {
            // Surrogates and values above U+10FFFF. TOML requires a scalar
            // value, and Rust's `char` cannot hold anything else, so this is
            // both a spec rule and a representability rule.
            Error::at(format!("`\\u{scalar:04X}` is not a Unicode scalar value"), line, column)
        })
    }

    // -- numbers and datetimes ---------------------------------------------

    fn parse_number_or_datetime(&mut self) -> Result<Kind, Error> {
        let (line, column) = self.here();
        let start = self.pos;
        while let Some(byte) = self.peek() {
            if is_value_terminator(byte) {
                break;
            }
            self.bump();
        }

        // `1979-05-27 07:32:00` — a space is a legal date/time separator, so a
        // bare token scan stops one token early. Reach across exactly one space
        // and only when what follows is unambiguously a time.
        if looks_like_date(&self.source[start..self.pos])
            && self.peek() == Some(b' ')
            && matches!(self.peek_at(1), Some(byte) if byte.is_ascii_digit())
            && matches!(self.peek_at(2), Some(byte) if byte.is_ascii_digit())
            && self.peek_at(3) == Some(b':')
        {
            self.bump();
            while let Some(byte) = self.peek() {
                if is_value_terminator(byte) {
                    break;
                }
                self.bump();
            }
        }

        let raw = &self.source[start..self.pos];
        if raw.is_empty() {
            return Err(Error::at("expected a value", line, column));
        }
        if looks_like_datetime(raw) {
            return Ok(Kind::Datetime(datetime::parse(raw, line, column)?));
        }
        parse_number(raw, line, column)
    }
}

fn finish_inline(builder: TableBuilder) -> Map<String, Item> {
    match builder.finish().kind {
        Kind::Table(table) => table,
        _ => unreachable!("a TableBuilder always finishes as a table"),
    }
}

// ---------------------------------------------------------------------------
// table identity
// ---------------------------------------------------------------------------

/// Walk to the active table. Every component is known to exist and to be a
/// table (or an array of tables, whose newest element is the active one),
/// because the path came from a header this parser itself just processed.
fn resolve_current<'t>(root: &'t mut TableBuilder, path: &[String]) -> &'t mut TableBuilder {
    let mut cursor = root;
    for name in path {
        cursor = match cursor.entries.get_mut(name) {
            Some(Slot::Table(table)) => table,
            Some(Slot::ArrayOfTables { items, .. }) => {
                items.last_mut().expect("an array of tables always has one element")
            }
            _ => unreachable!("the active table path is built by this parser"),
        };
    }
    cursor
}

/// Descend one ancestor component of a `[header]` path, creating an implicit
/// table if needed.
fn descend_header<'t>(
    cursor: &'t mut TableBuilder,
    part: &KeyPart,
) -> Result<&'t mut TableBuilder, Error> {
    if !cursor.entries.contains_key(&part.name) {
        cursor.entries.insert(
            part.name.clone(),
            Slot::Table(TableBuilder::new(TableKind::ImplicitHeader, part.line, part.column)),
        );
    }
    match cursor.entries.get_mut(&part.name).expect("just inserted if absent") {
        // Any table kind may be *passed through*. TOML v1.0.0 §Table permits
        // `[fruit.apple.texture]` after `fruit.apple` was created by a dotted
        // key; only redefining the dotted table itself is forbidden, and that
        // is checked in `open_table`.
        Slot::Table(table) => Ok(table),
        // `[[a]]` then `[a.b]` puts `b` inside the newest `a`.
        Slot::ArrayOfTables { items, .. } => {
            Ok(items.last_mut().expect("an array of tables always has one element"))
        }
        Slot::Value(item) => Err(Error::at(
            format!(
                "`{}` is already a {} (defined at line {}), so it cannot also be a table",
                part.name,
                item.kind.type_name(),
                item.line
            ),
            part.line,
            part.column,
        )),
    }
}

/// `[a]` — open a table explicitly.
fn open_table(
    cursor: &mut TableBuilder,
    part: &KeyPart,
    line: usize,
    column: usize,
) -> Result<(), Error> {
    match cursor.entries.get_mut(&part.name) {
        None => {
            cursor.entries.insert(
                part.name.clone(),
                Slot::Table(TableBuilder::new(TableKind::Explicit, line, column)),
            );
            Ok(())
        }
        Some(Slot::Table(table)) if table.kind == TableKind::ImplicitHeader => {
            // `[a.b]` then `[a]`: the ancestor was implied, and this header is
            // its one legal explicit definition.
            table.kind = TableKind::Explicit;
            table.line = line;
            table.column = column;
            Ok(())
        }
        Some(Slot::Table(table)) if table.kind == TableKind::ImplicitDotted => Err(Error::at(
            format!(
                "table `{}` was defined by a dotted key at line {}; TOML does not allow \
                 redefining it with a header (sub-tables of it are still allowed)",
                part.name, table.line
            ),
            part.line,
            part.column,
        )),
        Some(Slot::Table(table)) => Err(Error::at(
            format!("table `{}` is already defined at line {}", part.name, table.line),
            part.line,
            part.column,
        )),
        Some(Slot::ArrayOfTables { line: defined, .. }) => Err(Error::at(
            format!(
                "`{}` is an array of tables (defined at line {defined}); use `[[{}]]`",
                part.name, part.name
            ),
            part.line,
            part.column,
        )),
        Some(Slot::Value(item)) => Err(Error::at(
            format!(
                "`{}` is already a {} (defined at line {})",
                part.name,
                item.kind.type_name(),
                item.line
            ),
            part.line,
            part.column,
        )),
    }
}

/// `[[a]]` — append to an array of tables.
fn open_array_of_tables(
    cursor: &mut TableBuilder,
    part: &KeyPart,
    line: usize,
    column: usize,
) -> Result<(), Error> {
    match cursor.entries.get_mut(&part.name) {
        None => {
            cursor.entries.insert(
                part.name.clone(),
                Slot::ArrayOfTables {
                    items: vec![TableBuilder::new(TableKind::Explicit, line, column)],
                    line,
                    column,
                },
            );
            Ok(())
        }
        Some(Slot::ArrayOfTables { items, .. }) => {
            items.push(TableBuilder::new(TableKind::Explicit, line, column));
            Ok(())
        }
        Some(Slot::Table(table)) => Err(Error::at(
            format!(
                "`{}` is a table (defined at line {}), so `[[{}]]` cannot append to it",
                part.name, table.line, part.name
            ),
            part.line,
            part.column,
        )),
        Some(Slot::Value(item)) => Err(Error::at(
            format!(
                "`{}` is already a {} (defined at line {})",
                part.name,
                item.kind.type_name(),
                item.line
            ),
            part.line,
            part.column,
        )),
    }
}

/// Write `a.b.c = value` into `table`, creating dotted intermediates.
fn insert_dotted(table: &mut TableBuilder, keys: &[KeyPart], value: Item) -> Result<(), Error> {
    let (last, ancestors) = keys.split_last().expect("a key path has at least one part");
    let mut cursor = table;
    for part in ancestors {
        if !cursor.entries.contains_key(&part.name) {
            cursor.entries.insert(
                part.name.clone(),
                Slot::Table(TableBuilder::new(TableKind::ImplicitDotted, part.line, part.column)),
            );
        }
        // Probe with a SHARED borrow first. The obvious `match
        // cursor.entries.get_mut(..)` with a guard on `inner.kind` does not
        // borrow-check: the guard's mutable borrow is held into the following
        // arm. Splitting the decision from the descent costs one extra lookup
        // and keeps the rule readable.
        //
        // Only a table this same dotted-key mechanism created may be extended.
        // Reaching into a `[header]`-defined table from a dotted key in a
        // *different* table is what TOML forbids, and letting it through would
        // silently merge two tables the author deliberately kept apart.
        let rejection = match cursor.entries.get(&part.name).expect("just inserted if absent") {
            Slot::Table(inner) if inner.kind == TableKind::ImplicitDotted => None,
            Slot::Table(inner) => Some(format!(
                "`{}` is a table defined at line {}; a dotted key cannot add to it",
                part.name, inner.line
            )),
            Slot::ArrayOfTables { line, .. } => Some(format!(
                "`{}` is an array of tables (defined at line {line}); a dotted key cannot add to it",
                part.name
            )),
            Slot::Value(item) => Some(format!(
                "`{}` is already a {} (defined at line {})",
                part.name,
                item.kind.type_name(),
                item.line
            )),
        };
        if let Some(message) = rejection {
            return Err(Error::at(message, part.line, part.column));
        }
        cursor = match cursor.entries.get_mut(&part.name).expect("probed immediately above") {
            Slot::Table(inner) => inner,
            _ => unreachable!("the shared-borrow probe accepted only a dotted table"),
        };
    }

    if let Some(existing) = cursor.entries.get(&last.name) {
        let (what, defined) = match existing {
            Slot::Value(item) => (item.kind.type_name(), item.line),
            Slot::Table(table) => ("table", table.line),
            Slot::ArrayOfTables { line, .. } => ("array of tables", *line),
        };
        // The single most consequential rejection in TOML: without it, a
        // duplicated key is silently last-one-wins.
        return Err(Error::at(
            format!("duplicate key `{}`: already defined as a {what} at line {defined}", last.name),
            last.line,
            last.column,
        ));
    }
    cursor.entries.insert(last.name.clone(), Slot::Value(value));
    Ok(())
}

// ---------------------------------------------------------------------------
// lexical predicates and number parsing
// ---------------------------------------------------------------------------

/// Whether `byte` may appear in a bare (unquoted) key.
///
/// `pub(crate)` because the *writer* needs the same predicate: `crate::emit`
/// decides whether to quote a key by asking this exact function. A writer that
/// carried its own copy of "what a bare key looks like" would eventually
/// disagree with the reader, and the symptom would be a document this crate
/// emits and cannot parse.
pub(crate) fn is_bare_key_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'-'
}

/// Characters that end an unquoted value token.
fn is_value_terminator(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\r' | b'\n' | b',' | b']' | b'}' | b'#')
}

/// TOML forbids the C0 controls and DEL in strings and comments. Tab is
/// allowed; the newline characters are handled by the callers, which need to
/// distinguish "line break" from "stray control byte".
fn is_forbidden_control(value: char) -> bool {
    matches!(value, '\u{0}'..='\u{8}' | '\u{b}' | '\u{c}' | '\u{e}'..='\u{1f}' | '\u{7f}')
}

fn looks_like_date(raw: &str) -> bool {
    let bytes = raw.as_bytes();
    bytes.len() >= 10
        && bytes[..4].iter().all(u8::is_ascii_digit)
        && bytes[4] == b'-'
        && bytes[5..7].iter().all(u8::is_ascii_digit)
        && bytes[7] == b'-'
        && bytes[8..10].iter().all(u8::is_ascii_digit)
}

fn looks_like_time(raw: &str) -> bool {
    let bytes = raw.as_bytes();
    bytes.len() >= 8
        && bytes[..2].iter().all(u8::is_ascii_digit)
        && bytes[2] == b':'
        && bytes[3..5].iter().all(u8::is_ascii_digit)
        && bytes[5] == b':'
}

fn looks_like_datetime(raw: &str) -> bool {
    looks_like_date(raw) || looks_like_time(raw)
}

/// Classify and parse an unquoted numeric token.
fn parse_number(raw: &str, line: usize, column: usize) -> Result<Kind, Error> {
    let bad = |what: String| Error::at(what, line, column);

    let (negative, body) = match raw.as_bytes().first() {
        Some(b'-') => (true, &raw[1..]),
        Some(b'+') => (false, &raw[1..]),
        _ => (false, raw),
    };
    let signed = body.len() != raw.len();

    if body == "inf" {
        return Ok(Kind::Float(if negative { f64::NEG_INFINITY } else { f64::INFINITY }));
    }
    if body == "nan" {
        // TOML says the sign of a NaN is implementation-specific. `f64::NAN` is
        // positive; negating it gives a NaN with the sign bit set. Both compare
        // unequal to everything, including themselves, which is why the
        // corpus differential compares NaN by classification rather than by
        // value (see `tests/differential_corpus.rs`).
        return Ok(Kind::Float(if negative { -f64::NAN } else { f64::NAN }));
    }

    if body.starts_with("0x") || body.starts_with("0o") || body.starts_with("0b") {
        if signed {
            return Err(bad(format!("`{raw}` is not valid: a radix prefix cannot take a sign")));
        }
        let radix = match &body[..2] {
            "0x" => 16,
            "0o" => 8,
            _ => 2,
        };
        let digits = strip_underscores(&body[2..], line, column)?;
        if digits.is_empty() {
            return Err(bad(format!("`{raw}` has a radix prefix but no digits")));
        }
        let valid = digits.chars().all(|digit| digit.is_digit(radix));
        if !valid {
            return Err(bad(format!("`{raw}` is not a valid base-{radix} integer")));
        }
        return i64::from_str_radix(&digits, radix)
            .map(Kind::Integer)
            .map_err(|_| bad(format!("`{raw}` does not fit in a 64-bit signed integer")));
    }

    let is_float = body.contains('.') || body.contains('e') || body.contains('E');
    if is_float {
        return parse_float(raw, body, negative, line, column);
    }

    let digits = strip_underscores(body, line, column)?;
    validate_decimal_digits(raw, &digits, line, column)?;
    let text = if negative { format!("-{digits}") } else { digits };
    text.parse::<i64>()
        .map(Kind::Integer)
        .map_err(|_| bad(format!("`{raw}` does not fit in a 64-bit signed integer")))
}

fn parse_float(
    raw: &str,
    body: &str,
    negative: bool,
    line: usize,
    column: usize,
) -> Result<Kind, Error> {
    let bad = |what: String| Error::at(what, line, column);

    let (mantissa, exponent) = match body.find(['e', 'E']) {
        Some(index) => (&body[..index], Some(&body[index + 1..])),
        None => (body, None),
    };
    let (integer_part, fraction) = match mantissa.find('.') {
        Some(index) => (&mantissa[..index], Some(&mantissa[index + 1..])),
        None => (mantissa, None),
    };

    let integer_digits = strip_underscores(integer_part, line, column)?;
    validate_decimal_digits(raw, &integer_digits, line, column)?;

    let mut text = String::new();
    if negative {
        text.push('-');
    }
    text.push_str(&integer_digits);

    if let Some(fraction) = fraction {
        let digits = strip_underscores(fraction, line, column)?;
        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(bad(format!("`{raw}` needs at least one digit after the decimal point")));
        }
        text.push('.');
        text.push_str(&digits);
    }

    if let Some(exponent) = exponent {
        let (sign, magnitude) = match exponent.as_bytes().first() {
            Some(b'-') => ("-", &exponent[1..]),
            Some(b'+') => ("", &exponent[1..]),
            _ => ("", exponent),
        };
        let digits = strip_underscores(magnitude, line, column)?;
        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(bad(format!("`{raw}` needs at least one digit in the exponent")));
        }
        text.push('e');
        text.push_str(sign);
        // Leading zeros ARE permitted in an exponent, unlike in the integer
        // part — `1e05` is valid TOML.
        text.push_str(&digits);
    }

    let value = text.parse::<f64>().map_err(|_| bad(format!("`{raw}` is not a valid float")))?;

    // A decimal literal that overflows `f64` is REJECTED, not silently rounded
    // to infinity. `inf`/`-inf`/`nan` were returned above, so reaching here
    // with a non-finite value means the author wrote finite digits and got
    // infinity — `1e400` becoming `inf` is a value the document does not
    // contain, and a `#[serde(default)]`-shaped consumer never notices.
    //
    // FOUND BY THE ADVERSARIAL DIFFERENTIAL, and it is the direction that
    // matters: before this check we ACCEPTED `a = 1e400` (as `inf`) where the
    // incumbent returns `Err`. The corpus could not see it — exactly one of
    // 1381 corpus documents contains a float at all.
    //
    // This rule is SYMMETRIC and the incumbent's is not. `toml_edit 0.22.27`,
    // `src/parser/numbers.rs:203`, guards the same hazard with
    //
    //     .verify(|f: &f64| *f != f64::INFINITY)
    //
    // which compares against POSITIVE infinity only, so `a = -1e400` sails
    // through it and yields `-inf`. That is a one-sided guard over a two-way
    // hazard, not a considered decision — the crate's own test file carries
    // `// ("1e+400", f64::INFINITY),` commented out beside it. Matching the
    // asymmetry would mean copying a typo into a crate whose reason for
    // existing is that it is ours; `tests/adversarial.rs` therefore records
    // `-1e400` as this crate's ONE deliberate divergence from the incumbent,
    // names it, and fails if the divergence set ever grows.
    if value.is_infinite() {
        return Err(bad(format!("`{raw}` overflows a 64-bit float")));
    }
    Ok(Kind::Float(value))
}

/// Remove `_` separators, enforcing that each sits between two digits.
///
/// `1_000` is valid, `_1`, `1_`, `1__0` are not. Silently accepting them would
/// make this reader accept documents the incumbent rejects, which the
/// acceptance gate would catch — but only if such a document existed in the
/// corpus, and none does. Enforced structurally instead.
fn strip_underscores(raw: &str, line: usize, column: usize) -> Result<String, Error> {
    let mut out = String::with_capacity(raw.len());
    let bytes = raw.as_bytes();
    for (index, byte) in bytes.iter().enumerate() {
        if *byte == b'_' {
            let before = index.checked_sub(1).map(|previous| bytes[previous]);
            let after = bytes.get(index + 1).copied();
            let flanked = matches!(before, Some(value) if value.is_ascii_alphanumeric())
                && matches!(after, Some(value) if value.is_ascii_alphanumeric());
            if !flanked {
                return Err(Error::at(
                    format!("`{raw}`: `_` must sit between two digits"),
                    line,
                    column,
                ));
            }
            continue;
        }
        out.push(char::from(*byte));
    }
    Ok(out)
}

/// TOML forbids leading zeros in a decimal integer or in the integer part of a
/// float: `01` is an error, `0` is not.
fn validate_decimal_digits(
    raw: &str,
    digits: &str,
    line: usize,
    column: usize,
) -> Result<(), Error> {
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(Error::at(format!("`{raw}` is not a valid number"), line, column));
    }
    if digits.len() > 1 && digits.starts_with('0') {
        return Err(Error::at(
            format!("`{raw}` is not valid: leading zeros are not allowed"),
            line,
            column,
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table(source: &str) -> Map<String, Item> {
        match parse_document(source).expect("should parse").kind {
            Kind::Table(table) => table,
            other => panic!("expected a table, got {other:?}"),
        }
    }

    fn kind(source: &str, key: &str) -> Kind {
        table(source).get(key).expect("key should be present").kind.clone()
    }

    #[test]
    fn scalars() {
        assert_eq!(kind("a = 1", "a"), Kind::Integer(1));
        assert_eq!(kind("a = -0", "a"), Kind::Integer(0));
        assert_eq!(kind("a = +99", "a"), Kind::Integer(99));
        assert_eq!(kind("a = 1_000_000", "a"), Kind::Integer(1_000_000));
        assert_eq!(kind("a = 0xdead_beef", "a"), Kind::Integer(0xdead_beef));
        assert_eq!(kind("a = 0o755", "a"), Kind::Integer(0o755));
        assert_eq!(kind("a = 0b1010", "a"), Kind::Integer(0b1010));
        assert_eq!(kind("a = 1.23", "a"), Kind::Float(1.23));
        assert_eq!(kind("a = 1e6", "a"), Kind::Float(1e6));
        assert_eq!(kind("a = -2.5E-3", "a"), Kind::Float(-2.5E-3));
        assert_eq!(kind("a = true", "a"), Kind::Boolean(true));
        assert_eq!(kind("a = false", "a"), Kind::Boolean(false));
        assert_eq!(kind("a = 1e05", "a"), Kind::Float(1e5), "leading zeros are legal in exponents");
    }

    #[test]
    fn strings() {
        assert_eq!(kind(r#"a = "x""#, "a"), Kind::String("x".into()));
        assert_eq!(kind(r#"a = "\t\n\\\"""#, "a"), Kind::String("\t\n\\\"".into()));
        assert_eq!(kind(r#"a = "\u00e9""#, "a"), Kind::String("é".into()));
        assert_eq!(kind(r#"a = "\U0001F600""#, "a"), Kind::String("\u{1F600}".into()));
        assert_eq!(kind(r"a = 'C:\path\n'", "a"), Kind::String(r"C:\path\n".into()));
        assert_eq!(kind("a = \"\"\"\nline\n\"\"\"", "a"), Kind::String("line\n".into()));
        assert_eq!(kind("a = '''\nraw\\n\n'''", "a"), Kind::String("raw\\n\n".into()));
        assert_eq!(
            kind("a = \"\"\"one \\\n     two\"\"\"", "a"),
            Kind::String("one two".into()),
            "a line-ending backslash swallows the newline and the indentation"
        );
        assert_eq!(
            kind("a = \"\"\"\"\"\"\"", "a"),
            Kind::String("\"".into()),
            "four closing quotes mean the content ends with one quote"
        );
    }

    #[test]
    fn dotted_keys_nest() {
        let root = table("a.b.c = 1\na.b.d = 2\n");
        let Kind::Table(a) = &root["a"].kind else { panic!("a should be a table") };
        let Kind::Table(b) = &a["b"].kind else { panic!("a.b should be a table") };
        assert_eq!(b["c"].kind, Kind::Integer(1));
        assert_eq!(b["d"].kind, Kind::Integer(2));
        assert!(root.get("a.b.c").is_none(), "a dotted key must not become a flat key");
    }

    #[test]
    fn arrays_of_tables_accumulate() {
        let root = table("[[x]]\nn = 1\n\n[[x]]\nn = 2\n");
        let Kind::Array(items) = &root["x"].kind else { panic!("x should be an array") };
        assert_eq!(items.len(), 2);
        let Kind::Table(first) = &items[0].kind else { panic!() };
        let Kind::Table(second) = &items[1].kind else { panic!() };
        assert_eq!(first["n"].kind, Kind::Integer(1));
        assert_eq!(second["n"].kind, Kind::Integer(2));
    }

    #[test]
    fn header_reopens_only_implicit_ancestors() {
        // `[a]` after `[a.b]` is legal: `a` existed only implicitly.
        assert!(parse_document("[a.b]\nx = 1\n[a]\ny = 2\n").is_ok());
        // The same header twice is not.
        assert!(parse_document("[a]\n[a]\n").is_err());
        // Nor is a header over a table a dotted key created.
        assert!(parse_document("a.b = 1\n[a]\n").is_err());
        // But a sub-table of a dotted-key table is fine (TOML v1.0.0 §Table).
        assert!(
            parse_document("[f]\napple.color = 'red'\n[f.apple.texture]\nsmooth = true\n").is_ok()
        );
    }

    #[test]
    fn rejections() {
        let cases = [
            ("a = 1\na = 2\n", "duplicate key"),
            ("a = 01\n", "leading zero"),
            ("a = 1__0\n", "double underscore"),
            ("a = \"x\ny\"\n", "newline in a single-line string"),
            ("a = \"\\q\"\n", "unknown escape"),
            ("a = {x = 1,}\n", "trailing comma in an inline table"),
            ("a = {x = 1,\ny = 2}\n", "newline in an inline table"),
            ("a = [1, 2\n", "unterminated array"),
            ("a = 1 b = 2\n", "two statements on one line"),
            ("[a]\n[[a]]\n", "array header over a table"),
            ("a = 2026-02-30\n", "impossible date"),
            ("a = \n", "missing value"),
            ("= 1\n", "missing key"),
            ("a = +0x1\n", "signed radix prefix"),
        ];
        for (source, why) in cases {
            let result = parse_document(source);
            assert!(result.is_err(), "{why}: {source:?} should be rejected");
            let error = result.unwrap_err();
            assert!(error.line().is_some(), "{why}: error must carry a line number");
        }
    }

    #[test]
    fn trailing_comma_in_an_array_is_allowed() {
        assert_eq!(
            kind("a = [1, 2, ]", "a"),
            Kind::Array(vec![
                Item { kind: Kind::Integer(1), line: 1, column: 6 },
                Item { kind: Kind::Integer(2), line: 1, column: 9 },
            ])
        );
    }

    #[test]
    fn positions_point_at_the_value() {
        let root = table("# comment\nalpha = 1\nbeta = \"two\"\n");
        assert_eq!((root["alpha"].line, root["alpha"].column), (2, 9));
        assert_eq!((root["beta"].line, root["beta"].column), (3, 8));
    }

    #[test]
    fn datetimes_round_trip() {
        for text in [
            "1979-05-27T07:32:00Z",
            "1979-05-27T00:32:00-07:00",
            "1979-05-27T07:32:00",
            "1979-05-27",
            "07:32:00",
            "07:32:00.999999",
        ] {
            let Kind::Datetime(parsed) = kind(&format!("a = {text}"), "a") else {
                panic!("{text} should parse as a datetime");
            };
            assert_eq!(parsed.to_string(), text, "{text} should round-trip");
        }
        // The one documented lossy case: trailing fractional zeros.
        let Kind::Datetime(parsed) = kind("a = 07:32:00.100", "a") else { panic!() };
        assert_eq!(parsed.to_string(), "07:32:00.1");
        // And the space separator, which normalizes to `T` exactly as the
        // incumbent's Display does.
        let Kind::Datetime(parsed) = kind("a = 1979-05-27 07:32:00", "a") else { panic!() };
        assert_eq!(parsed.to_string(), "1979-05-27T07:32:00");
    }
}
