//! Stable names for Lean declarations: `<qualified name>#<16 hex>`, the same
//! shape as a Rust obligation key ([`crate::obligation_identity`]), so a
//! `trust.obligations.v1` record of a `.lean` check is keyed, compared and
//! diffed exactly as a crate's is.
//!
//! # What a key is
//!
//! The def-path half is the canonical name Clean's elaborator assigned the
//! declaration (its namespaces applied). A declaration Clean names nothing
//! (`example`) uses its keyword in that place, so several of them share a def
//! path and are told apart by their local ids.
//!
//! The local id is the first sixteen hex digits of
//!
//! ```text
//! SHA-256( LEAN_DECLARATION_ID_DOMAIN ‖ lp(keyword) ‖ lp(anchor) ‖ u32le(nth) )
//! ```
//!
//! where the ANCHOR is the declaration's statement — its tokens from the
//! keyword to the first `:=`, `where` or `|` outside brackets (the whole
//! declaration when there is none), with the declared name left out — and
//! `nth` is its rank among the declarations of the same qualified name,
//! keyword and anchor, in source order.
//!
//! So the key names the CLAIM: editing a proof keeps the key (the row's status
//! moves under the same name), editing the statement makes a new key (the old
//! claim vanished and a new one appeared), and renaming keeps the local id
//! (a comparison can pair the declaration by its id or its source digest).
//!
//! # Source text is read as TOKENS
//!
//! [`lean_tokens`] drops whitespace and comments (`--` lines and nested
//! `/- … -/` blocks, doc comments included) and splits identifiers, numbers,
//! strings, brackets and runs of other symbols apart, so a reformat — a
//! reindent, a reflowed statement, `(a:Nat)` to `(a : Nat)`, a comment added or
//! edited — moves neither a key nor the declaration's source digest
//! ([`LeanDeclaration::source_digest`]).
//!
//! # Where a declaration is
//!
//! This module reads no command structure. Which commands a file has, where
//! each one is and what its canonical name is (namespaces applied) are what
//! Clean's own parse and elaboration report
//! (`trust_certify::clean_island::CleanIslandDeclaration`); the caller passes
//! each command's name and source text to [`lean_declarations`], which only
//! reads the declaration keyword, the statement and the tokens out of it. A
//! command with no declaration keyword (`open`, `#check`, `notation`) is not a
//! declaration and gets no key.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use sha2::{Digest, Sha256};

use crate::digest::lowercase_hex;
use crate::obligation_identity::{LOCAL_ID_HEX_LEN, obligation_key};

/// Domain separator of a Lean declaration's local id.
pub const LEAN_DECLARATION_ID_DOMAIN: &[u8] = b"trust-lean-declaration-id/v1\0";

/// Domain separator of a Lean declaration's source digest.
pub const LEAN_DECLARATION_SOURCE_DOMAIN: &[u8] = b"trust-lean-declaration-source/v1\0";

/// Keywords that open a declaration.
const DECLARATION_KEYWORDS: &[&str] = &[
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "example",
    "axiom",
    "opaque",
    "structure",
    "inductive",
    "class",
];

/// The declarations that are named by their keyword, not by a name of their own.
const ANONYMOUS_KEYWORDS: &[&str] = &["example"];

fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_' || c == '«'
}

fn is_ident_continue(c: char) -> bool {
    c.is_alphanumeric()
        || matches!(c, '_' | '\'' | '!' | '?')
        || ('\u{2080}'..='\u{209c}').contains(&c)
}

fn is_bracket(c: char) -> bool {
    matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | '⟨' | '⟩' | '⦃' | '⦄' | ',')
}

/// The byte ranges of the tokens of Lean source `text`: whitespace and
/// comments are not tokens (module docs).
#[must_use]
pub fn lean_tokens(text: &str) -> Vec<(usize, usize)> {
    let mut tokens = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some(&(start, c)) = chars.peek() {
        let rest = &text[start..];
        if c.is_whitespace() {
            chars.next();
        } else if rest.starts_with("--") {
            while chars.peek().is_some_and(|&(_, c)| c != '\n') {
                chars.next();
            }
        } else if rest.starts_with("/-") {
            let mut depth = 0usize;
            let mut index = start;
            loop {
                let here = &text[index..];
                if here.is_empty() {
                    break;
                }
                if here.starts_with("/-") {
                    depth += 1;
                    index += 2;
                } else if here.starts_with("-/") {
                    depth -= 1;
                    index += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    index += here.chars().next().map_or(1, char::len_utf8);
                }
            }
            while chars.peek().is_some_and(|&(at, _)| at < index) {
                chars.next();
            }
        } else if c == '"' {
            chars.next();
            let mut escaped = false;
            let mut end = text.len();
            for (at, c) in chars.by_ref() {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == '"' {
                    end = at + 1;
                    break;
                }
            }
            tokens.push((start, end));
        } else if c == '«' {
            chars.next();
            let mut end = text.len();
            for (at, c) in chars.by_ref() {
                if c == '»' {
                    end = at + c.len_utf8();
                    break;
                }
            }
            // A quoted segment may continue a dotted name.
            let end = continue_identifier(text, end, &mut chars);
            tokens.push((start, end));
        } else if is_ident_start(c) {
            chars.next();
            let end = continue_identifier(text, start + c.len_utf8(), &mut chars);
            tokens.push((start, end));
        } else if c.is_ascii_digit() {
            let mut end = start;
            while let Some(&(at, c)) = chars.peek() {
                if c.is_ascii_alphanumeric() || c == '_' || (c == '.' && end > start) {
                    // `1.5` is one number; `x.1` reads `x`, `.`, `1`.
                    if c == '.'
                        && !text[at + 1..].chars().next().is_some_and(|n| n.is_ascii_digit())
                    {
                        break;
                    }
                    end = at + c.len_utf8();
                    chars.next();
                } else {
                    break;
                }
            }
            tokens.push((start, end));
        } else if is_bracket(c) {
            chars.next();
            tokens.push((start, start + c.len_utf8()));
        } else {
            let mut end = start;
            while let Some(&(at, c)) = chars.peek() {
                let here = &text[at..];
                if c.is_whitespace()
                    || is_ident_start(c)
                    || c.is_ascii_digit()
                    || is_bracket(c)
                    || c == '"'
                    || (at > start && (here.starts_with("--") || here.starts_with("/-")))
                {
                    break;
                }
                end = at + c.len_utf8();
                chars.next();
            }
            tokens.push((start, end));
        }
    }
    tokens
}

/// Extend an identifier ending at `end` over its remaining characters and any
/// `.segment` continuations.
fn continue_identifier(
    text: &str,
    mut end: usize,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> usize {
    loop {
        match chars.peek() {
            Some(&(at, c)) if at == end && is_ident_continue(c) => {
                end = at + c.len_utf8();
                chars.next();
            }
            Some(&(at, '.'))
                if at == end && text[at + 1..].chars().next().is_some_and(is_ident_start) =>
            {
                chars.next();
                end = at + 1;
                if text[end..].starts_with('«') {
                    for (at, c) in chars.by_ref() {
                        if c == '»' {
                            end = at + c.len_utf8();
                            break;
                        }
                    }
                }
            }
            _ => return end,
        }
    }
}

/// The token text of `text`, one space between tokens.
#[must_use]
pub fn lean_token_text(text: &str) -> String {
    join(text, &lean_tokens(text))
}

fn join(text: &str, tokens: &[(usize, usize)]) -> String {
    let mut out = String::new();
    for (index, (start, end)) in tokens.iter().enumerate() {
        if index > 0 {
            out.push(' ');
        }
        out.push_str(&text[*start..*end]);
    }
    out
}

/// One Lean declaration of a source file, named.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanDeclaration {
    /// The declaration keyword (`theorem`, `def`, …).
    pub keyword: String,
    /// The def-path half of the key: Clean's canonical name, or the keyword
    /// for a declaration with none (`example`).
    pub name: String,
    /// The statement tokens, the name left out (module docs).
    pub anchor: String,
    /// SHA-256 over [`LEAN_DECLARATION_SOURCE_DOMAIN`] and every token of the
    /// declaration except its name, as 64 lowercase hex digits: a reformat is
    /// not a source change, an edit of the proof is.
    pub source_digest: String,
    /// The sixteen-hex local id.
    pub local_id: String,
}

impl LeanDeclaration {
    /// `<qualified name>#<local id>`.
    #[must_use]
    pub fn key(&self) -> String {
        obligation_key(&self.name, &self.local_id)
    }
}

/// The local id of the `nth` declaration with `keyword` and `anchor`.
#[must_use]
pub fn lean_declaration_id(keyword: &str, anchor: &str, nth: u32) -> String {
    let mut hasher = Sha256::new();
    hasher.update(LEAN_DECLARATION_ID_DOMAIN);
    for field in [keyword, anchor] {
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field.as_bytes());
    }
    hasher.update(nth.to_le_bytes());
    lowercase_hex(&hasher.finalize()[..LOCAL_ID_HEX_LEN / 2])
}

/// The keyword, statement anchor and source digest of one command's source
/// text, or `None` when it declares nothing (no declaration keyword outside
/// brackets).
fn shape(text: &str) -> Option<(String, String, String)> {
    let tokens = lean_tokens(text);
    let token = |i: usize| tokens.get(i).map(|&(s, e)| &text[s..e]);
    let mut depth = 0i64;
    let mut keyword = None;
    for index in 0..tokens.len() {
        match token(index).unwrap_or_default() {
            "(" | "[" | "{" | "⟨" | "⦃" => depth += 1,
            ")" | "]" | "}" | "⟩" | "⦄" => depth -= 1,
            t if depth <= 0 && DECLARATION_KEYWORDS.contains(&t) => {
                keyword = Some(index);
                break;
            }
            _ => {}
        }
    }
    let keyword = keyword?;
    // `class inductive` reads as one keyword.
    let (keyword, keyword_text) = match (token(keyword).unwrap_or_default(), token(keyword + 1)) {
        ("class", Some("inductive")) => (keyword + 1, "class inductive"),
        (text, _) => (keyword, text),
    };
    let name_index = (!ANONYMOUS_KEYWORDS.contains(&keyword_text)
        && token(keyword + 1)
            .is_some_and(|t| t.chars().next().is_some_and(is_ident_start) && t != "where"))
    .then_some(keyword + 1);
    // The statement: keyword to the first `:=`, `where` or `|` at bracket
    // depth zero.
    let mut depth = 0i64;
    let mut header_end = tokens.len();
    for index in keyword + 1..tokens.len() {
        match token(index).unwrap_or_default() {
            "(" | "[" | "{" | "⟨" | "⦃" => depth += 1,
            ")" | "]" | "}" | "⟩" | "⦄" => depth -= 1,
            ":=" | "where" | "|" if depth <= 0 => {
                header_end = index;
                break;
            }
            _ => {}
        }
    }
    let statement: Vec<(usize, usize)> = (keyword..header_end)
        .filter(|index| Some(*index) != name_index)
        .map(|index| tokens[index])
        .collect();
    let body: Vec<(usize, usize)> = (0..tokens.len())
        .filter(|index| Some(*index) != name_index)
        .map(|index| tokens[index])
        .collect();
    let mut hasher = Sha256::new();
    hasher.update(LEAN_DECLARATION_SOURCE_DOMAIN);
    hasher.update(join(text, &body).as_bytes());
    Some((keyword_text.to_string(), join(text, &statement), lowercase_hex(&hasher.finalize())))
}

/// The source text of each command Clean listed in `text`, in authored order:
/// `spans` are Clean's `(start, end)` byte offsets of each command (its
/// keyword), and a command's text runs from its start to the line the next
/// listed command starts on (the end of the text for the last), which leaves
/// that command's attributes and `set_option … in` to it. `None` for a
/// command whose span does not lie in `text`: a command no record can read,
/// never a guess. One copy, shared by a `.lean` file's records and a crate's
/// island rows, so the two lanes slice a declaration alike.
#[must_use]
pub fn lean_command_texts<'a>(text: &'a str, spans: &[(usize, usize)]) -> Vec<Option<&'a str>> {
    spans
        .iter()
        .enumerate()
        .map(|(index, &(start, end))| {
            let next = spans.get(index + 1).map_or(text.len(), |next| next.0);
            let line_of_next = text.get(..next)?.rfind('\n').map_or(0, |at| at + 1);
            let stop = if line_of_next > end { line_of_next } else { next };
            text.get(start..stop.max(end))
        })
        .collect()
}

/// Name the commands of one file, in authored order. Each command is the
/// canonical name Clean gave it (`None` for an `example`, a `mutual` block, a
/// lexical command) and its source text as Clean's span covers it. The result
/// has one entry per command: `None` for a command that declares nothing.
#[must_use]
pub fn lean_declarations<'a>(
    commands: impl IntoIterator<Item = (Option<&'a str>, &'a str)>,
) -> Vec<Option<LeanDeclaration>> {
    let mut counts: BTreeMap<(String, String, String), u32> = BTreeMap::new();
    commands
        .into_iter()
        .map(|(name, text)| {
            let (keyword, anchor, source_digest) = shape(text)?;
            let name = match name {
                Some(name) => name.strip_prefix("_root_.").unwrap_or(name).to_string(),
                None => keyword.rsplit(' ').next().unwrap_or(&keyword).to_string(),
            };
            let nth = counts.entry((name.clone(), keyword.clone(), anchor.clone())).or_insert(0);
            let local_id = lean_declaration_id(&keyword, &anchor, *nth);
            *nth += 1;
            Some(LeanDeclaration { keyword, name, anchor, source_digest, local_id })
        })
        .collect()
}

#[cfg(test)]
#[path = "lean_declaration_identity_tests.rs"]
mod tests;
