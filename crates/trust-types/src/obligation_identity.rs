//! The stable, content-addressed obligation key (work item T9).
//!
//! # What a key is
//!
//! `<def_path>#<local id>`: the function's def path, then sixteen lowercase hex
//! digits that name ONE obligation inside that function. [`local_ids`] mints the
//! local ids, once, for a function's whole row set; it is the only minting
//! function, and the compiler calls it at transport emission (the one place that
//! has the source text an anchor needs).
//!
//! The local id is the first sixteen hex digits of
//!
//! ```text
//! SHA-256( OBLIGATION_ID_DOMAIN ‖ lp(kind) ‖ lp(anchor) ‖ u32le(nth) )
//! ```
//!
//! where `lp` is a little-endian `u64` length prefix, `kind` is the row's compact
//! kind tag (`divzero`, `overflow:add`, …), the ANCHOR is what the obligation is
//! about in the source ([`anchor`]), and `nth` is the row's rank among the
//! function's rows with the same `(kind, anchor)`: in order of the span's START,
//! then by the row's content ([`row_discriminator`]), and only then in emission
//! order.
//!
//! # Source text is read as TOKENS
//!
//! Every anchor and the function source digest are computed from the Rust
//! token stream ([`tokens`]), with whitespace and comments dropped and the
//! tokens joined by one space. A reformat — `a/b` to `a / b`, `f(a,b)` to
//! `f(a, b)`, a call reflowed across lines or back onto one, a comment added or
//! edited — therefore moves neither a key nor the digest, and the digest and
//! the anchors agree on what an edit is: a change to the token stream.
//!
//! # Why this shape
//!
//! The private ordinal `obligation_id` (`vc:<fn>:<kind>:<carrier index>`) stays
//! what it is — the binding and certificate token `docs/TCB.md` names — and is
//! never a comparison key again. It failed as one for three measured reasons,
//! pinned by `tests/obligation_key_divergence_pin.rs`:
//!
//! * one carrier index per function, shared by every kind, so adding or removing
//!   any obligation renumbered every later one;
//! * one source division mints TWO rows of one kind at one stored span (twins);
//! * checked-add and macro rows carry degenerate point spans (`lo == hi`).
//!
//! Here no position and no ordinal enters the key. The anchor is the statement
//! around the span's START ([`statement_tokens`]), so a line inserted above the
//! function, or inside it above the obligation, leaves the key alone; twins
//! differ only in `nth`, which counts rows with the same kind AND the same
//! anchor, so a twin pair renumbers only itself, and twins whose content
//! differs keep their order whatever order the compiler emits them in.
//!
//! # Only the span's START is identity
//!
//! The END of a row's span is not a property of the obligation: the same
//! `let x = a / b;` division is published as a point at `a` (`lo == hi`) by one
//! compile and as the range `a / b` by another, and which one a function gets can
//! turn on an unrelated edit (measured 2026-10-10 by
//! `tests/run-make/trust-obligation-ids`: `f`'s rows were points with one
//! division in the body and ranges once a second division was inserted above it,
//! and an anchor that read the range's tokens moved every key of `f`). So the
//! anchor and the `nth` order read the start alone (an END is still checked to lie
//! in the text and, for a range, to cover a token) — the start-only projection
//! the tree's span identities already make (trust-router's `SealedVcIdentity`,
//! `trust_r1_oracle`'s `span_line_col`). The cost is a coarser anchor: an edit
//! elsewhere in an obligation's own statement moves its key.
//!
//! The def path stays OUTSIDE the hash, so a moved function keeps its local ids
//! and a baseline can match the move by its source digest
//! ([`function_source_digest`]) or by the ids themselves.
//!
//! A duplicate local id inside one function is a refused mint
//! ([`IdCollision`]), never a silent merge.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::fmt;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::SourceSpan;
use crate::digest::lowercase_hex;

/// Domain separator of a local id. `v2` (2026-10-10): the anchor and the `nth`
/// order read a span's START alone (module docs); a `v1` id is not comparable.
pub const OBLIGATION_ID_DOMAIN: &[u8] = b"trust-obligation-id/v2\0";

/// Domain separator of a function's source digest.
pub const FUNCTION_SOURCE_DOMAIN: &[u8] = b"trust-function-source/v1\0";

/// The number of hex digits in a local id.
pub const LOCAL_ID_HEX_LEN: usize = 16;

/// The separator between the def path and the local id in a key.
pub const KEY_SEPARATOR: char = '#';

/// One obligation's identity as a consumer reads it: the key, the package the
/// obligation belongs to, and its function's source digest.
///
/// This record does not confer authority. Expanded-input provenance is also
/// bound independently in the original claim snapshot before proof replay.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ObligationIdentity {
    /// `<def_path>#<local id>` ([`obligation_key`]).
    pub key: String,
    /// The Cargo package the obligation was compiled for, or, outside Cargo,
    /// the crate name.
    pub package: String,
    /// The function's [`function_source_digest`], when the compiler stated it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function_source_sha256: Option<String>,
    /// Distinct compiler-captured expanded input provenance. Never interpreted
    /// as an ordinary function-source text hash.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expanded_function_identity:
        Option<crate::expanded_function_identity::ExpandedFunctionIdentity>,
}

impl ObligationIdentity {
    /// The def-path half of the key.
    #[must_use]
    pub fn def_path(&self) -> &str {
        split_obligation_key(&self.key).map_or(self.key.as_str(), |(def_path, _)| def_path)
    }
}

fn needs_whitespace_collapse(text: &str) -> bool {
    let bytes = text.as_bytes();
    let Some(&first) = bytes.first() else {
        return false;
    };
    if first.is_ascii_whitespace() || !first.is_ascii() {
        return true;
    }
    if bytes.last().is_some_and(|&b| b.is_ascii_whitespace() || !b.is_ascii()) {
        return true;
    }
    let mut prev_space = false;
    for &b in bytes {
        if !b.is_ascii() {
            return true;
        }
        if b == b' ' {
            if prev_space {
                return true;
            }
            prev_space = true;
        } else if b.is_ascii_whitespace() {
            return true;
        } else {
            prev_space = false;
        }
    }
    false
}

fn collapse_whitespace_cow(text: &str) -> std::borrow::Cow<'_, str> {
    if !needs_whitespace_collapse(text) {
        return std::borrow::Cow::Borrowed(text);
    }
    let mut out = String::with_capacity(text.len());
    for (index, word) in text.split_whitespace().enumerate() {
        if index > 0 {
            out.push(' ');
        }
        out.push_str(word);
    }
    std::borrow::Cow::Owned(out)
}

/// Collapse every run of whitespace to one space and trim the ends.
#[must_use]
pub fn collapse_whitespace(text: &str) -> String {
    collapse_whitespace_cow(text).into_owned()
}

/// The first [`LOCAL_ID_HEX_LEN`] lowercase hex digits of SHA-256 over `bytes`.
#[must_use]
pub fn sha16(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    lowercase_hex(&digest[..LOCAL_ID_HEX_LEN / 2])
}

/// A row description with its volatile parts removed: whitespace collapsed,
/// MIR locals (`_12`) written `_`, and hash-like suffixes (`@` followed by eight
/// or more hex digits) written `@#`. Used only by the anchor of a row that has
/// no source location.
#[must_use]
pub fn normalize_description(description: &str) -> String {
    normalize_description_cow(description).into_owned()
}

fn normalize_description_cow(description: &str) -> std::borrow::Cow<'_, str> {
    let collapsed = collapse_whitespace_cow(description);
    let bytes = collapsed.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut out: Option<String> = None;
    let mut copied_until = 0usize;
    let mut index = 0usize;
    while index < bytes.len() {
        let b = bytes[index];
        if b == b'_' && (index == 0 || !is_ident(bytes[index - 1])) {
            let digits = bytes[index + 1..].iter().take_while(|&&b| b.is_ascii_digit()).count();
            let after = bytes.get(index + 1 + digits).copied();
            if digits > 0 && !after.is_some_and(|b| b.is_ascii_alphabetic() || b == b'_') {
                let buf = out.get_or_insert_with(|| String::with_capacity(collapsed.len()));
                buf.push_str(&collapsed[copied_until..=index]);
                index += 1 + digits;
                copied_until = index;
                continue;
            }
        }
        if b == b'@' {
            let hex = bytes[index + 1..].iter().take_while(|&&b| b.is_ascii_hexdigit()).count();
            if hex >= 8 {
                let buf = out.get_or_insert_with(|| String::with_capacity(collapsed.len()));
                buf.push_str(&collapsed[copied_until..index]);
                buf.push_str("@#");
                index += 1 + hex;
                copied_until = index;
                continue;
            }
        }
        index += 1;
    }
    match out {
        Some(mut buf) => {
            buf.push_str(&collapsed[copied_until..]);
            std::borrow::Cow::Owned(buf)
        }
        None => collapsed,
    }
}

/// A rendered file name outside the package, reduced to a checkout-independent
/// form: `@sysroot/<path>` for the toolchain's own sources, `@registry/<crate
/// dir>/<path>` for a registry checkout, `@git/<path>` for a git checkout, and
/// `@crate/<dir>/src/<path>` (or the relative path as rendered) for anything
/// else. The input is the producer's `stable_obligation_file` rendering.
#[must_use]
pub fn normalize_external_path(file: &str) -> String {
    for prefix in ["/rustc/<toolchain>/", "/rustc-dev/<toolchain>/"] {
        if let Some(tail) = file.strip_prefix(prefix) {
            return format!("@sysroot/{tail}");
        }
    }
    if let Some(at) = file.find("/lib/rustlib/src/rust/") {
        return format!("@sysroot/{}", &file[at + "/lib/rustlib/src/rust/".len()..]);
    }
    if let Some(rest) = file.strip_prefix("<cargo-home>/registry/src/")
        && let Some((_index, tail)) = rest.split_once('/')
    {
        return format!("@registry/{tail}");
    }
    if let Some(at) = file.find("/git/checkouts/") {
        let rest = &file[at + "/git/checkouts/".len()..];
        // `<repo>-<hash>/<rev>/<path>`: both directory names are checkout-local.
        let mut parts = rest.splitn(3, '/');
        let (_repo, _rev, tail) = (parts.next(), parts.next(), parts.next());
        if let Some(tail) = tail {
            return format!("@git/{tail}");
        }
    }
    if !file.starts_with('/') {
        return format!("@crate/{file}");
    }
    match file.rfind("/src/") {
        Some(at) => {
            let dir_start = file[..at].rfind('/').map_or(0, |slash| slash + 1);
            format!("@crate/{}", &file[dir_start..])
        }
        None => format!("@crate/{}", file.rsplit('/').next().unwrap_or(file)),
    }
}

/// The byte ranges of the Rust tokens of `text`, in order, with whitespace and
/// comments (line, block — nested — and doc comments) dropped.
///
/// A deliberately small lexer: it only has to cut the text where rustc would
/// and never inside a literal, so that whitespace and comments are the ONLY
/// things it removes. String literals of every form (`"…"`, `b"…"`, `c"…"`,
/// raw `r#"…"#`, with escapes), character and byte literals and lifetimes are
/// one token each, so a `//` or a run of spaces inside a literal is content.
/// Identifiers (raw ones included) and numbers (suffix, fraction and exponent
/// included) are one token each; every other character is a token of its own,
/// so `>>` and `> >` read alike — which no reformat can produce from different
/// code. It never fails: an unterminated literal or comment runs to the end.
#[must_use]
pub fn tokens(text: &str) -> Vec<(usize, usize)> {
    let mut out = Vec::with_capacity(text.len() / 4);
    let mut at = 0;
    while let Some(c) = text[at..].chars().next() {
        let rest = &text[at..];
        if c.is_whitespace() {
            at += c.len_utf8();
            continue;
        }
        if rest.starts_with("//") {
            at += rest.find('\n').unwrap_or(rest.len());
            continue;
        }
        if rest.starts_with("/*") {
            at += block_comment_len(rest);
            continue;
        }
        let len = literal_len(rest)
            .or_else(|| (c == '\'').then(|| quote_len(rest)))
            .unwrap_or_else(|| {
                if c.is_ascii_digit() {
                    number_len(rest)
                } else if is_ident_char(c) {
                    ident_len(rest)
                } else {
                    c.len_utf8()
                }
            });
        out.push((at, at + len));
        at += len;
    }
    out
}

/// `text` as its tokens joined by one space: the form every anchor and the
/// function source digest hash.
#[must_use]
pub fn token_text(text: &str) -> String {
    join_tokens(text, &tokens(text))
}

fn join_tokens(text: &str, tokens: &[(usize, usize)]) -> String {
    if tokens.is_empty() {
        return String::new();
    }
    let len: usize =
        tokens.iter().map(|&(start, end)| end - start).sum::<usize>() + tokens.len() - 1;
    let mut out = String::with_capacity(len);
    for (index, &(start, end)) in tokens.iter().enumerate() {
        if index > 0 {
            out.push(' ');
        }
        out.push_str(&text[start..end]);
    }
    out
}

fn sha16_tokens(text: &str, tokens: &[(usize, usize)]) -> String {
    let mut hasher = Sha256::new();
    let bytes = text.as_bytes();
    for (index, &(start, end)) in tokens.iter().enumerate() {
        if index > 0 {
            hasher.update(b" ");
        }
        hasher.update(&bytes[start..end]);
    }
    let digest = hasher.finalize();
    lowercase_hex(&digest[..LOCAL_ID_HEX_LEN / 2])
}

fn is_ident_char(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
}

fn ident_len(rest: &str) -> usize {
    // A raw identifier `r#name` is one token.
    let skip = if rest.starts_with("r#") && rest[2..].chars().next().is_some_and(is_ident_char) {
        2
    } else {
        0
    };
    skip + rest[skip..].find(|c: char| !is_ident_char(c)).unwrap_or(rest.len() - skip)
}

fn number_len(rest: &str) -> usize {
    let bytes = rest.as_bytes();
    let radix_prefixed =
        rest.len() > 1 && bytes[0] == b'0' && matches!(bytes[1], b'x' | b'o' | b'b');
    let mut at = 0;
    loop {
        while at < bytes.len() && (bytes[at].is_ascii_alphanumeric() || bytes[at] == b'_') {
            at += 1;
        }
        let exponent_sign = !radix_prefixed
            && at > 0
            && matches!(bytes[at - 1], b'e' | b'E')
            && bytes.get(at).is_some_and(|b| matches!(b, b'+' | b'-'))
            && bytes.get(at + 1).is_some_and(u8::is_ascii_digit);
        let fraction = bytes.get(at) == Some(&b'.')
            && bytes.get(at + 1).is_some_and(u8::is_ascii_digit)
            && !rest[..at].contains('.');
        if exponent_sign || fraction {
            at += 1;
            continue;
        }
        return at;
    }
}

fn block_comment_len(rest: &str) -> usize {
    let bytes = rest.as_bytes();
    let mut depth = 0usize;
    let mut at = 0;
    while at < bytes.len() {
        if bytes[at..].starts_with(b"/*") {
            depth += 1;
            at += 2;
        } else if bytes[at..].starts_with(b"*/") {
            depth -= 1;
            at += 2;
            if depth == 0 {
                return at;
            }
        } else {
            at += 1;
        }
    }
    rest.len()
}

/// The length of a string, byte-string, C-string or raw-string literal, or of a
/// byte literal `b'x'`, starting at `rest`; `None` when `rest` does not start one.
fn literal_len(rest: &str) -> Option<usize> {
    let bytes = rest.as_bytes();
    let mut at = usize::from(matches!(bytes.first(), Some(b'b' | b'c')));
    if at == 1 && bytes.get(1) == Some(&b'\'') && bytes[0] == b'b' {
        return Some(1 + quote_len(&rest[1..]));
    }
    if bytes.get(at) == Some(&b'r') {
        at += 1;
        let hashes = bytes[at..].iter().take_while(|&&b| b == b'#').count();
        at += hashes;
        if bytes.get(at) != Some(&b'"') {
            return None;
        }
        at += 1;
        const CLOSE_STATIC: &str = "\"########";
        if hashes + 1 <= CLOSE_STATIC.len() {
            let close = &CLOSE_STATIC[..=hashes];
            return Some(rest[at..].find(close).map_or(rest.len(), |end| at + end + close.len()));
        }
        let close: String = std::iter::once('"').chain(std::iter::repeat_n('#', hashes)).collect();
        return Some(rest[at..].find(&close).map_or(rest.len(), |end| at + end + close.len()));
    }
    if bytes.get(at) != Some(&b'"') {
        return None;
    }
    at += 1;
    while at < bytes.len() {
        match bytes[at] {
            b'\\' => at += 2,
            b'"' => return Some(at + 1),
            _ => at += 1,
        }
    }
    Some(rest.len())
}

/// The length of a character literal or a lifetime starting with `'` at `rest`.
fn quote_len(rest: &str) -> usize {
    let mut chars = rest.char_indices().skip(1);
    let Some((_, first)) = chars.next() else { return rest.len() };
    if first == '\\' {
        // An escaped character literal: up to the closing quote.
        let mut escaped = true;
        for (at, c) in rest.char_indices().skip(2) {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '\'' {
                return at + 1;
            }
        }
        return rest.len();
    }
    match chars.next() {
        // `'x'`: a character literal.
        Some((at, '\'')) => at + 1,
        // `'name`: a lifetime or label.
        _ if is_ident_char(first) => 1 + ident_len(&rest[1..]),
        _ => 1,
    }
}

/// Byte offsets of the start of every line of a source text (lines are split
/// at `\n`, as rustc's normalized sources are), and the text's [`tokens`].
/// Built once per file; every anchor in that file reads it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineIndex {
    starts: Vec<usize>,
    tokens: Vec<(usize, usize)>,
}

impl LineIndex {
    /// Index `text`.
    #[must_use]
    pub fn new(text: &str) -> Self {
        let mut starts = Vec::with_capacity(text.len() / 32 + 1);
        starts.push(0);
        starts.extend(text.match_indices('\n').map(|(at, _)| at + 1));
        Self { starts, tokens: tokens(text) }
    }

    /// Line `line` (1-based), without its line break.
    #[must_use]
    pub fn line<'a>(&self, text: &'a str, line: u32) -> Option<&'a str> {
        let (start, end) = self.line_range(text, line)?;
        text.get(start..end)
    }

    fn line_range(&self, text: &str, line: u32) -> Option<(usize, usize)> {
        let index = usize::try_from(line).ok()?.checked_sub(1)?;
        let start = *self.starts.get(index)?;
        let end = self.starts.get(index + 1).map_or(text.len(), |next| next - 1);
        Some((start, end))
    }

    /// The byte offset of character column `col` (0-based, rustc's
    /// `lookup_char_pos` column) on line `line` (1-based). The column may be
    /// one past the line's last character (an exclusive end).
    #[must_use]
    pub fn offset(&self, text: &str, line: u32, col: u32) -> Option<usize> {
        let (start, end) = self.line_range(text, line)?;
        let line_text = text.get(start..end)?;
        let col = usize::try_from(col).ok()?;
        if line_text.is_ascii() {
            return (col <= line_text.len()).then_some(start + col);
        }
        let mut chars = line_text.char_indices();
        for _ in 0..col {
            chars.next()?;
        }
        Some(start + chars.next().map_or(line_text.len(), |(at, _)| at))
    }

    /// The text `span` covers (exclusive end), or `None` when the span does not
    /// lie inside `text`.
    #[must_use]
    pub fn span_text<'a>(&self, text: &'a str, span: &SourceSpan) -> Option<&'a str> {
        let (lo, hi) = self.span_offsets(text, span)?;
        text.get(lo..hi)
    }

    fn span_offsets(&self, text: &str, span: &SourceSpan) -> Option<(usize, usize)> {
        let lo = self.offset(text, span.line_start, span.col_start)?;
        let hi = self.offset(text, span.line_end, span.col_end)?;
        (lo <= hi && text.get(lo..hi).is_some()).then_some((lo, hi))
    }

    /// Whether at least one token overlaps the byte range `lo..hi`.
    fn has_tokens_in(&self, lo: usize, hi: usize) -> bool {
        let first = self.tokens.partition_point(|&(_, end)| end <= lo);
        self.tokens.get(first).is_some_and(|&(start, _)| start < hi)
    }

    /// The token slice overlapping the byte range `lo..hi`.
    fn tokens_slice_in(&self, lo: usize, hi: usize) -> &[(usize, usize)] {
        let first = self.tokens.partition_point(|&(_, end)| end <= lo);
        let last = first + self.tokens[first..].partition_point(|&(start, _)| start < hi);
        &self.tokens[first..last]
    }

    /// The statement token slice around byte offset `at`, as [`statement_tokens`] reads it.
    fn statement_slice_at(&self, text: &str, at: usize) -> &[(usize, usize)] {
        let point = self.tokens.partition_point(|&(_, end)| end <= at);
        let (first, last) = statement_tokens(text, &self.tokens, point);
        &self.tokens[first..last]
    }
}

/// The token index range of the statement that contains token `point` (every
/// local span's anchor, read at the span's start: see the module docs on why
/// only the start is identity).
///
/// Read lexically, never from a line, so a reflow moves nothing:
///
/// * when `point` sits inside a `( … )` or `[ … ]` group, the statement is the
///   one that contains that group (a call's arguments, a closure passed to it,
///   an index expression), found the same way from the group's opener;
/// * otherwise it runs back to the nearest `;`, `{`, `}` or `,` at the same
///   nesting level and forward to the nearest `;`, `{`, `}`, `)`, `]` or `,`
///   at that level, stepping over balanced `( … )` and `[ … ]` groups. A `,`
///   ends it so a match arm or a struct field stands alone; a `{` ends it so
///   an `if` or `while` condition does not take its block along.
///
/// The range is coarser than the obligation (it is a statement, not an
/// expression), so `nth` still separates the rows that share it.
#[must_use]
pub fn statement_tokens(text: &str, tokens: &[(usize, usize)], point: usize) -> (usize, usize) {
    let token = |index: usize| -> &str {
        let (start, end) = tokens[index];
        &text[start..end]
    };
    if point >= tokens.len() {
        return (tokens.len(), tokens.len());
    }
    // The nearest unmatched opener before `point`.
    let mut depth = 0usize;
    let mut enclosing = None;
    for index in (0..point).rev() {
        match token(index) {
            ")" | "]" | "}" => depth += 1,
            "(" | "[" | "{" if depth > 0 => depth -= 1,
            "(" | "[" | "{" => {
                enclosing = Some(index);
                break;
            }
            _ => {}
        }
    }
    if let Some(opener) = enclosing.filter(|&opener| matches!(token(opener), "(" | "[")) {
        return statement_tokens(text, tokens, opener);
    }
    let mut first = point;
    while first > 0 {
        match token(first - 1) {
            ";" | "{" | "}" | "," => break,
            ")" | "]" => first = matching_opener(text, tokens, first - 1),
            _ => first -= 1,
        }
    }
    let mut last = point;
    while last < tokens.len() {
        match token(last) {
            ";" | "{" | "}" | ")" | "]" | "," => break,
            "(" | "[" => last = matching_closer(text, tokens, last) + 1,
            _ => last += 1,
        }
    }
    (first, last)
}

/// The index of the opener that matches the closer at `closer`, or 0.
fn matching_opener(text: &str, tokens: &[(usize, usize)], closer: usize) -> usize {
    let mut depth = 0usize;
    for index in (0..=closer).rev() {
        match &text[tokens[index].0..tokens[index].1] {
            ")" | "]" | "}" => depth += 1,
            "(" | "[" | "{" => {
                depth -= 1;
                if depth == 0 {
                    return index;
                }
            }
            _ => {}
        }
    }
    0
}

/// The index of the closer that matches the opener at `opener`, or the last
/// token.
fn matching_closer(text: &str, tokens: &[(usize, usize)], opener: usize) -> usize {
    let mut depth = 0usize;
    for (index, &(start, end)) in tokens.iter().enumerate().skip(opener) {
        match &text[start..end] {
            "(" | "[" | "{" => depth += 1,
            ")" | "]" | "}" => {
                depth -= 1;
                if depth == 0 {
                    return index;
                }
            }
            _ => {}
        }
    }
    tokens.len() - 1
}

/// What a row's anchor is computed from.
#[derive(Debug, Clone, Copy)]
pub enum AnchorInput<'a> {
    /// The row carries no source location.
    Unlocated {
        /// The row's description.
        description: &'a str,
    },
    /// The row's file is not a source file of the package being compiled.
    External {
        /// The rendered file name.
        file: &'a str,
    },
    /// The row's file is a source file of the package being compiled.
    Local {
        /// The row's span.
        span: &'a SourceSpan,
        /// The whole file's (normalized) text.
        text: &'a str,
        /// `text`'s line and token index.
        lines: &'a LineIndex,
    },
}

impl<'a> AnchorInput<'a> {
    /// The input for a row with `location` and `description`, given the local
    /// source text of the location's file when the file is the package's own.
    /// A location with an empty file (the dummy span) is no location.
    #[must_use]
    pub fn of(
        location: Option<&'a SourceSpan>,
        description: &'a str,
        local_source: Option<(&'a str, &'a LineIndex)>,
    ) -> Self {
        match location.filter(|span| !span.file.is_empty()) {
            None => Self::Unlocated { description },
            Some(span) => match local_source {
                Some((text, lines)) => Self::Local { span, text, lines },
                None => Self::External { file: &span.file },
            },
        }
    }
}

/// Why an anchor could not be computed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnchorError {
    /// The file the span names.
    pub file: String,
    /// The span, as `line:col-line:col`.
    pub span: String,
}

impl fmt::Display for AnchorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "span {} does not lie inside the source text of `{}`, or covers no token",
            self.span, self.file
        )
    }
}

impl std::error::Error for AnchorError {}

/// Whether `span` is a point (`lo == hi`).
#[must_use]
pub fn is_point_span(span: &SourceSpan) -> bool {
    span.line_start == span.line_end && span.col_start == span.col_end
}

/// The anchor of one row: what the obligation is about, with no position.
///
/// * `stmt:<sha16>` — the token text of the statement around a local span's
///   START ([`statement_tokens`]), whether the span is a point or a range: the
///   end is not the obligation's (module docs);
/// * `ext:<path>` — a span outside the package: the normalized path only
///   ([`normalize_external_path`]);
/// * `none:<sha16>` — a row with no location: its [`normalize_description`].
///
/// # Errors
///
/// A local span that does not lie inside its file's text, a range that covers
/// no token, or a start with no statement around it (past the last token) — a
/// producer defect.
pub fn anchor(input: AnchorInput<'_>) -> Result<String, AnchorError> {
    match input {
        AnchorInput::Unlocated { description } => {
            Ok(format!("none:{}", sha16(normalize_description_cow(description).as_bytes())))
        }
        AnchorInput::External { file } => Ok(format!("ext:{}", normalize_external_path(file))),
        AnchorInput::Local { span, text, lines } => {
            let error = || AnchorError {
                file: span.file.clone(),
                span: format!(
                    "{}:{}-{}:{}",
                    span.line_start, span.col_start, span.line_end, span.col_end
                ),
            };
            let (lo, hi) = lines.span_offsets(text, span).ok_or_else(error)?;
            if !is_point_span(span) && !lines.has_tokens_in(lo, hi) {
                return Err(error());
            }
            let statement = lines.statement_slice_at(text, lo);
            if statement.is_empty() {
                return Err(error());
            }
            Ok(format!("stmt:{}", sha16_tokens(text, statement)))
        }
    }
}

/// The anchor the compiler mints with, and whether it had to be DEGRADED.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RowAnchor {
    /// The anchor.
    pub anchor: String,
    /// `true` when [`anchor`] refused the row's span and the anchor is the
    /// coarser fallback. The compiler counts these
    /// (`CoverageTransportSummary::degraded_anchors`), so a run whose keys are
    /// coarser than a content address says so.
    pub degraded: bool,
}

/// The anchor the compiler mints with: [`anchor`], DEGRADED rather than
/// refused when a local span does not lie inside its file's text (a span whose
/// two ends were rendered from different files) or covers no token: the
/// tokens of the span's start line when that line exists, otherwise its file as
/// an external anchor. An anchor is identity, never authority, so a degraded
/// anchor can only make a key coarser — its `nth` still separates the rows
/// that share it — and a single odd span never costs a whole function its
/// keys. A degraded anchor is never silent: [`RowAnchor::degraded`].
#[must_use]
pub fn row_anchor(input: AnchorInput<'_>) -> RowAnchor {
    if let Ok(anchor) = anchor(input) {
        return RowAnchor { anchor, degraded: false };
    }
    let anchor = match input {
        AnchorInput::Local { span, text, lines } => match lines.line_range(text, span.line_start) {
            Some((start, end)) => {
                format!("line:{}", sha16_tokens(text, lines.tokens_slice_in(start, end)))
            }
            None => format!("ext:{}", normalize_external_path(&span.file)),
        },
        AnchorInput::Unlocated { description } => {
            format!("none:{}", sha16(normalize_description_cow(description).as_bytes()))
        }
        AnchorInput::External { file } => format!("ext:{}", normalize_external_path(file)),
    };
    RowAnchor { anchor, degraded: true }
}

/// What tells two rows with the same kind, anchor and position apart before
/// emission order does: the row's [`normalize_description`] (MIR locals and
/// hash suffixes erased). Rows whose descriptions differ keep their relative
/// order — and so their `nth` — whatever order the compiler emits them in.
#[must_use]
pub fn row_discriminator(description: &str) -> String {
    normalize_description(description)
}

/// The local id of the `nth` row with `kind` and `anchor`.
#[must_use]
pub fn local_id(kind: &str, anchor: &str, nth: u32) -> String {
    let mut hasher = Sha256::new();
    hasher.update(OBLIGATION_ID_DOMAIN);
    for field in [kind, anchor] {
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field.as_bytes());
    }
    hasher.update(nth.to_le_bytes());
    let digest = hasher.finalize();
    lowercase_hex(&digest[..LOCAL_ID_HEX_LEN / 2])
}

/// A span's position, the order `nth` counts in: its START, `(line_start,
/// col_start)` — the end is not the obligation's (module docs). A row with no location sorts first.
pub type SpanPosition = (u32, u32);

/// The position of an optional span.
#[must_use]
pub fn span_position(span: Option<&SourceSpan>) -> SpanPosition {
    span.map_or((0, 0), |span| (span.line_start, span.col_start))
}

/// One row of a function, as [`local_ids`] reads it.
#[derive(Debug, Clone, Copy)]
pub struct KeyedRow<'a> {
    /// The compact kind tag.
    pub kind: &'a str,
    /// The row's [`anchor`].
    pub anchor: &'a str,
    /// The row's [`span_position`].
    pub position: SpanPosition,
    /// The row's [`row_discriminator`].
    pub discriminator: &'a str,
}

/// Two rows of one function minted the same local id.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdCollision {
    /// The colliding local id.
    pub id: String,
    /// The two rows' indices, in emission order.
    pub rows: (usize, usize),
}

impl fmt::Display for IdCollision {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "obligation rows {} and {} minted the same local id `{}`; no row of this function \
             carries a stable key",
            self.rows.0, self.rows.1, self.id
        )
    }
}

impl std::error::Error for IdCollision {}

/// Mint the local id of every row of ONE function. `rows` is the function's
/// whole row set in emission order; the result is in the same order. Within a
/// `(kind, anchor)` group, `nth` ranks rows by position, then by
/// discriminator, then by emission order — so emission order decides only
/// between rows that agree on everything the compiler states about them.
///
/// # Errors
///
/// Two rows minted the same local id. The `(kind, anchor, nth)` triples are
/// distinct by construction, so this is a 64-bit truncation collision; it is
/// refused rather than merged.
pub fn local_ids(rows: &[KeyedRow<'_>]) -> Result<Vec<String>, IdCollision> {
    mint_local_ids(rows, local_id)
}

/// [`local_ids`] with the id function as a parameter, so the refusal of a
/// collision is exercised with a real colliding mint.
fn mint_local_ids(
    rows: &[KeyedRow<'_>],
    mint: impl Fn(&str, &str, u32) -> String,
) -> Result<Vec<String>, IdCollision> {
    match rows {
        [] => return Ok(Vec::new()),
        [only] => return Ok(vec![mint(only.kind, only.anchor, 0)]),
        _ => {}
    }
    let mut order: Vec<usize> = (0..rows.len()).collect();
    order.sort_by(|&a, &b| {
        let key = |index: usize| {
            let row = &rows[index];
            (row.kind, row.anchor, row.position, row.discriminator, index)
        };
        key(a).cmp(&key(b))
    });
    let mut ids = vec![String::new(); rows.len()];
    let mut previous: Option<(&str, &str)> = None;
    let mut nth = 0u32;
    for index in order {
        let group = (rows[index].kind, rows[index].anchor);
        nth = if previous == Some(group) { nth + 1 } else { 0 };
        previous = Some(group);
        ids[index] = mint(group.0, group.1, nth);
    }
    let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
    for (index, id) in ids.iter().enumerate() {
        if let Some(&first) = seen.get(id.as_str()) {
            return Err(IdCollision { id: id.clone(), rows: (first, index) });
        }
        seen.insert(id, index);
    }
    Ok(ids)
}

/// `<def_path>#<local id>`.
#[must_use]
pub fn obligation_key(def_path: &str, local_id: &str) -> String {
    format!("{def_path}{KEY_SEPARATOR}{local_id}")
}

/// Whether `id` is a well-formed local id: exactly [`LOCAL_ID_HEX_LEN`]
/// lowercase hex digits.
#[must_use]
pub fn is_local_id(id: &str) -> bool {
    id.len() == LOCAL_ID_HEX_LEN
        && id.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// Split a key into its def path and local id. A def path may itself contain
/// `#` (`{closure#0}`), so the split is at the LAST separator, and the local id
/// must be well formed.
#[must_use]
pub fn split_obligation_key(key: &str) -> Option<(&str, &str)> {
    let (def_path, id) = key.rsplit_once(KEY_SEPARATOR)?;
    (!def_path.is_empty() && is_local_id(id)).then_some((def_path, id))
}

/// The digest of a function's source: SHA-256 over [`FUNCTION_SOURCE_DOMAIN`]
/// and the [`token_text`] of the item, as 64 lowercase hex digits. Whitespace
/// and comments are not tokens, so a reformat or a comment edit is not a source
/// change; anything that changes the token stream is — the same rule every
/// anchor follows, so "unchanged source" and "unchanged keys" agree.
#[must_use]
pub fn function_source_digest(text: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(FUNCTION_SOURCE_DOMAIN);
    let bytes = text.as_bytes();
    for (index, (start, end)) in tokens(text).into_iter().enumerate() {
        if index > 0 {
            hasher.update(b" ");
        }
        hasher.update(&bytes[start..end]);
    }
    lowercase_hex(&hasher.finalize())
}

/// Whether `digest` is a well-formed [`function_source_digest`].
#[must_use]
pub fn is_function_source_digest(digest: &str) -> bool {
    digest.len() == 64 && digest.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

#[cfg(test)]
#[path = "obligation_identity_tests.rs"]
mod tests;
