// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The one error type this crate produces, re-exported as [`crate::de::Error`].
//!
//! # What a good TOML error has to say
//!
//! Two things, and this type enforces both structurally rather than by
//! convention:
//!
//! * **a line number**, because the caller is looking at a file; and
//! * **the offending key**, when one is in scope, because "invalid type:
//!   integer" over a 40-key manifest is not a diagnosis.
//!
//! Positions are filled in at the point that knows them and never overwritten:
//! [`Error::with_position`] and [`Error::with_key`] are *fill-if-absent*. The
//! innermost frame that knows a fact wins, so a value's own span beats the
//! enclosing table's span, and a key attached by the map accessor is not
//! clobbered by an outer accessor.
//!
//! # Deliberate deviation from the incumbent: message TEXT is not compatible
//!
//! `toml 0.8` renders errors through `toml_edit`'s diagnostic machinery and
//! produces a specific multi-line rendering. This crate renders its own. The
//! acceptance gate (`tests/rejection.rs`) therefore asserts **accept/reject
//! agreement only**, never text equality: over-fitting to another crate's prose
//! makes its next release a build break here, and it would pin us to wording we
//! do not control. If you find yourself asserting on `Display` output against
//! the incumbent, you are testing the wrong contract.
//!
//! What *is* asserted, independently of the incumbent, is that every rendering
//! carries a line number, and a key whenever one was in scope.

use std::fmt;

/// An error produced while reading TOML.
///
/// Boxed inner state keeps `Result<T, Error>` one word wider than `T` on the
/// happy path. Errors here are rare and cold; the size of the success case is
/// what every caller pays.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    inner: Box<Inner>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Inner {
    message: String,
    line: Option<usize>,
    /// 1-based, counted in `char`s, not bytes — a caret under byte 30 of a
    /// line containing non-ASCII points at the wrong place.
    column: Option<usize>,
    key: Option<String>,
    /// The source line the position names, captured at the `from_str` boundary
    /// (see [`Error::attach_source`]). The parser itself does not carry it,
    /// because errors raised inside serde's derived visitors never pass through
    /// the parser.
    snippet: Option<String>,
}

impl Error {
    pub(crate) fn new(message: impl Into<String>) -> Self {
        Self {
            inner: Box::new(Inner {
                message: message.into(),
                line: None,
                column: None,
                key: None,
                snippet: None,
            }),
        }
    }

    pub(crate) fn at(message: impl Into<String>, line: usize, column: usize) -> Self {
        let mut error = Self::new(message);
        error.inner.line = Some(line);
        error.inner.column = Some(column);
        error
    }

    /// Fill the position **if it is not already set**.
    ///
    /// Fill-if-absent, not overwrite: an error raised at a value's own span
    /// must not be relabelled with the enclosing table's span as it unwinds.
    #[must_use]
    pub(crate) fn with_position(mut self, line: usize, column: usize) -> Self {
        if self.inner.line.is_none() {
            self.inner.line = Some(line);
            self.inner.column = Some(column);
        }
        self
    }

    /// Fill the key **if it is not already set**. See [`Self::with_position`].
    #[must_use]
    pub(crate) fn with_key(mut self, key: &str) -> Self {
        if self.inner.key.is_none() {
            self.inner.key = Some(key.to_string());
        }
        self
    }

    /// Capture the source line named by [`Self::line`], for rendering.
    ///
    /// Called once, at the `from_str` boundary, which is the only place that
    /// still holds the input. Cheap because it runs only on the error path.
    pub(crate) fn attach_source(mut self, source: &str) -> Self {
        if self.inner.snippet.is_none()
            && let Some(line) = self.inner.line
            && let Some(text) = source.lines().nth(line.saturating_sub(1))
        {
            self.inner.snippet = Some(text.to_string());
        }
        self
    }

    /// The 1-based line, if known.
    #[must_use]
    pub fn line(&self) -> Option<usize> {
        self.inner.line
    }

    /// The 1-based column in `char`s, if known.
    #[must_use]
    pub fn column(&self) -> Option<usize> {
        self.inner.column
    }

    /// The key the failure is about, if one was in scope.
    #[must_use]
    pub fn key(&self) -> Option<&str> {
        self.inner.key.as_deref()
    }

    /// The bare message, without position or key decoration.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.inner.message
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = &self.inner;
        match (inner.line, inner.column) {
            (Some(line), Some(column)) => {
                writeln!(f, "TOML parse error at line {line}, column {column}")?;
                if let Some(snippet) = &inner.snippet {
                    let gutter = line.to_string();
                    let pad = " ".repeat(gutter.len());
                    writeln!(f, "{pad} |")?;
                    writeln!(f, "{gutter} | {snippet}")?;
                    // `column` is 1-based in chars; the caret sits under it.
                    writeln!(f, "{pad} | {}^", " ".repeat(column.saturating_sub(1)))?;
                }
            }
            (Some(line), None) => writeln!(f, "TOML parse error at line {line}")?,
            _ => write!(f, "TOML parse error: ")?,
        }
        write!(f, "{}", inner.message)?;
        if let Some(key) = &inner.key {
            write!(f, " (in key `{key}`)")?;
        }
        Ok(())
    }
}

impl std::error::Error for Error {}

impl serde::de::Error for Error {
    fn custom<T: fmt::Display>(message: T) -> Self {
        // Everything serde's derived code raises — `unknown field`, `missing
        // field`, `unknown variant`, `invalid type`, `invalid length` — arrives
        // here with no position. The position is attached as the error unwinds
        // through this crate's `MapAccess`/`SeqAccess`/`deserialize_struct`,
        // each of which knows a span the derived code does not.
        Self::new(message.to_string())
    }
}
