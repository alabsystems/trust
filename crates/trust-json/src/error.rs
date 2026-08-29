// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Parse and serialize errors.
//!
//! The `Display` texts and the line/column arithmetic are transcribed from the
//! incumbent, because they are already user-visible: `targo trust` prints them,
//! and two crates in this tree put a JSON error inside a `#[from]` chain. The
//! differential asserts accept/reject agreement and the line/column pair; the
//! message texts are asserted for the enumerated table in
//! `tests/differential_json.rs` because they are transcribed, not invented.

use core::fmt::{self, Debug, Display};

/// Alias for a `Result` with the error type [`Error`].
pub type Result<T> = core::result::Result<T, Error>;

/// Categorizes the cause of a JSON error.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Category {
    /// The error was caused by a failure to read or write bytes on an I/O
    /// stream.
    Io,
    /// The error was caused by input that was not syntactically valid JSON.
    Syntax,
    /// The error was caused by input data that was semantically incorrect.
    Data,
    /// The error was caused by prematurely reaching the end of the input data.
    Eof,
}

#[derive(Debug)]
pub(crate) enum ErrorCode {
    Message(Box<str>),
    Io(std::io::Error),
    EofWhileParsingList,
    EofWhileParsingObject,
    EofWhileParsingString,
    EofWhileParsingValue,
    ExpectedColon,
    ExpectedListCommaOrEnd,
    ExpectedObjectCommaOrEnd,
    ExpectedSomeIdent,
    ExpectedSomeValue,
    InvalidEscape,
    InvalidNumber,
    NumberOutOfRange,
    InvalidUnicodeCodePoint,
    ControlCharacterWhileParsingString,
    KeyMustBeAString,
    LoneLeadingSurrogateInHexEscape,
    TrailingComma,
    TrailingCharacters,
    UnexpectedEndOfHexEscape,
    RecursionLimitExceeded,
}

impl Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorCode::Message(msg) => f.write_str(msg),
            ErrorCode::Io(err) => Display::fmt(err, f),
            ErrorCode::EofWhileParsingList => f.write_str("EOF while parsing a list"),
            ErrorCode::EofWhileParsingObject => f.write_str("EOF while parsing an object"),
            ErrorCode::EofWhileParsingString => f.write_str("EOF while parsing a string"),
            ErrorCode::EofWhileParsingValue => f.write_str("EOF while parsing a value"),
            ErrorCode::ExpectedColon => f.write_str("expected `:`"),
            ErrorCode::ExpectedListCommaOrEnd => f.write_str("expected `,` or `]`"),
            ErrorCode::ExpectedObjectCommaOrEnd => f.write_str("expected `,` or `}`"),
            ErrorCode::ExpectedSomeIdent => f.write_str("expected ident"),
            ErrorCode::ExpectedSomeValue => f.write_str("expected value"),
            ErrorCode::InvalidEscape => f.write_str("invalid escape"),
            ErrorCode::InvalidNumber => f.write_str("invalid number"),
            ErrorCode::NumberOutOfRange => f.write_str("number out of range"),
            ErrorCode::InvalidUnicodeCodePoint => f.write_str("invalid unicode code point"),
            ErrorCode::ControlCharacterWhileParsingString => {
                f.write_str("control character (\\u0000-\\u001F) found while parsing a string")
            }
            ErrorCode::KeyMustBeAString => f.write_str("key must be a string"),
            ErrorCode::LoneLeadingSurrogateInHexEscape => {
                f.write_str("lone leading surrogate in hex escape")
            }
            ErrorCode::TrailingComma => f.write_str("trailing comma"),
            ErrorCode::TrailingCharacters => f.write_str("trailing characters"),
            ErrorCode::UnexpectedEndOfHexEscape => f.write_str("unexpected end of hex escape"),
            ErrorCode::RecursionLimitExceeded => f.write_str("recursion limit exceeded"),
        }
    }
}

/// This type represents all possible errors that can occur when serializing or
/// deserializing JSON data.
pub struct Error {
    err: Box<ErrorImpl>,
}

struct ErrorImpl {
    code: ErrorCode,
    line: usize,
    column: usize,
}

impl Error {
    /// One-based line number at which the error was detected.
    #[must_use]
    pub fn line(&self) -> usize {
        self.err.line
    }

    /// One-based column number at which the error was detected.
    #[must_use]
    pub fn column(&self) -> usize {
        self.err.column
    }

    /// Categorizes the cause of this error.
    #[must_use]
    pub fn classify(&self) -> Category {
        match self.err.code {
            ErrorCode::Message(_) => Category::Data,
            ErrorCode::Io(_) => Category::Io,
            ErrorCode::EofWhileParsingList
            | ErrorCode::EofWhileParsingObject
            | ErrorCode::EofWhileParsingString
            | ErrorCode::EofWhileParsingValue => Category::Eof,
            ErrorCode::ExpectedColon
            | ErrorCode::ExpectedListCommaOrEnd
            | ErrorCode::ExpectedObjectCommaOrEnd
            | ErrorCode::ExpectedSomeIdent
            | ErrorCode::ExpectedSomeValue
            | ErrorCode::InvalidEscape
            | ErrorCode::InvalidNumber
            | ErrorCode::NumberOutOfRange
            | ErrorCode::InvalidUnicodeCodePoint
            | ErrorCode::ControlCharacterWhileParsingString
            | ErrorCode::KeyMustBeAString
            | ErrorCode::LoneLeadingSurrogateInHexEscape
            | ErrorCode::TrailingComma
            | ErrorCode::TrailingCharacters
            | ErrorCode::UnexpectedEndOfHexEscape
            | ErrorCode::RecursionLimitExceeded => Category::Syntax,
        }
    }

    #[must_use]
    pub fn is_io(&self) -> bool {
        self.classify() == Category::Io
    }
    #[must_use]
    pub fn is_syntax(&self) -> bool {
        self.classify() == Category::Syntax
    }
    #[must_use]
    pub fn is_data(&self) -> bool {
        self.classify() == Category::Data
    }
    #[must_use]
    pub fn is_eof(&self) -> bool {
        self.classify() == Category::Eof
    }

    pub(crate) fn syntax(code: ErrorCode, line: usize, column: usize) -> Self {
        Error {
            err: Box::new(ErrorImpl { code, line, column }),
        }
    }

    pub(crate) fn io(error: std::io::Error) -> Self {
        Error {
            err: Box::new(ErrorImpl {
                code: ErrorCode::Io(error),
                line: 0,
                column: 0,
            }),
        }
    }

    /// Builds a data error the way `serde::de::Error::custom` does, so the
    /// serde layer can hand one back without inventing a second error type.
    pub fn custom<T: Display>(msg: T) -> Self {
        Error {
            err: Box::new(ErrorImpl {
                code: ErrorCode::Message(msg.to_string().into_boxed_str()),
                line: 0,
                column: 0,
            }),
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.err.line == 0 {
            Display::fmt(&self.err.code, f)
        } else {
            write!(
                f,
                "{} at line {} column {}",
                self.err.code, self.err.line, self.err.column
            )
        }
    }
}

impl Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Error({:?}, line: {}, column: {})",
            self.err.code.to_string(),
            self.err.line,
            self.err.column
        )
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.err.code {
            ErrorCode::Io(err) => Some(err),
            _ => None,
        }
    }
}

impl From<Error> for std::io::Error {
    fn from(j: Error) -> Self {
        let category = j.classify();
        if matches!(j.err.code, ErrorCode::Io(_)) {
            match j.err.code {
                ErrorCode::Io(err) => err,
                // `matches!` above already decided this.
                _ => unreachable!(),
            }
        } else {
            match category {
                Category::Io => unreachable!(),
                Category::Syntax | Category::Data => {
                    std::io::Error::new(std::io::ErrorKind::InvalidData, j)
                }
                Category::Eof => std::io::Error::new(std::io::ErrorKind::UnexpectedEof, j),
            }
        }
    }
}
