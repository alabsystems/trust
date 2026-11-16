//! Trust: lexing the body of a `clean { … }` PARSER ISLAND as Clean (Lean)
//! bytes rather than as Rust tokens.
//!
//! The island is REALLY PARSED by the real Clean parser at rustc parse time
//! (ruling v7/D1), and `docs/TWO_LANGUAGE_100_PERCENT_GOAL.md` G2 says what
//! that implies for the lexical layer: *"A Rust token tree is not the lexical
//! boundary of the Lean language."* Before this module existed it was.
//! `lex_token_trees` tokenizes a whole file eagerly, so the island body met
//! the RUST lexer first: a `≤` became `unknown start of token`, a `"` inside a
//! Lean `--` comment opened a Rust string literal that swallowed the rest of
//! the file, and a `}` inside any Lean comment or string ended the island
//! early — all before `Parser::parse_clean_island` could run. The out-of-line
//! `clean mod name;` unit never had the problem, because its `.clean` file is
//! handed to the Clean parser as raw text; the inline form must get the same
//! treatment, and it can only get it HERE, because the lexer is the first
//! thing that touches the bytes.
//!
//! # What this module decides, and what it does not
//!
//! Two questions, answered separately so each stays exact:
//!
//! 1. **Is this `clean` the start of an island?** Only at MODULE ITEM
//!    position — the one place the parser's island arm is reached
//!    (`parse_mod` and the item loops that share its position; a
//!    statement-position `clean { f: 1 }` is a struct literal and never
//!    reaches it). The lexer knows the delimiter stack and the previous
//!    token at each level, which is enough to answer this without parsing:
//!    every enclosing delimiter must be a `mod name { … }` body (or there is
//!    none), no enclosing delimiter may be a macro's or attribute's token
//!    tree, and the token before `clean` must be one that can precede an
//!    item and nothing else. Every rule fails CLOSED — an unrecognised shape
//!    lexes as it always did. `clean` is not a keyword, and the constraint
//!    is that all valid Rust keeps compiling identically: a struct named
//!    `clean` in `let s = clean { f: 1 }`, `static S: clean = clean { f: 1 }`,
//!    `fn f() -> clean { clean { f: 1 } }` and `stringify!(clean { f: 1 })`
//!    is untouched, and `tests/ui/trust/clean_island_rust_identity.rs` pins
//!    each of those.
//!
//!    Islands are only ever recognised when the source is lexed as a module
//!    root (`StripTokens::ShebangAndFrontmatter`) — the crate root,
//!    an out-of-line `mod name;` file, and `include!` in item position. That
//!    is exactly the rule frontmatter already follows for the same reason:
//!    a region that is not Rust tokens may only be recognised where the
//!    parser will treat the surrounding text as items.
//!
//! 2. **Where does the island end?** Found by `scan_clean_island_body`, a
//!    Lean-aware scanner: `--` line comments, nested `/- … -/` block
//!    comments, `"…"` strings with `\` escapes, `r#"…"#` raw strings,
//!    `'x'` char literals (distinguished from identifier primes such as
//!    `h'`), `«…»` names, and nested `{ … }` (Lean structure instances,
//!    implicit binders, set-builder notation) are all opaque; only a
//!    structural `}` at depth zero closes the island. Nothing inside is
//!    interpreted — the bytes go to the Clean parser verbatim through the
//!    source map, and whether they are Lean is the Clean parser's verdict.
//!
//! The token tree the lexer emits for an island is an EMPTY
//! `Delimited(Brace)` whose open/close spans are the real braces.
//! `Parser::parse_clean_island` derives the body span from those delimiter
//! spans, never from inner tokens, so a token round trip (an attribute
//! proc-macro passing the item through) recovers the same bytes from the
//! source map. An island the lexer did not recognise — inside a macro
//! invocation's token trees, say — still reaches the parser as ordinary
//! Rust tokens, and the parser derives the same span the same way.

use rustc_ast::token::{self, Delimiter, IdentKind, Token};
use rustc_ast::tokenstream::{DelimSpacing, DelimSpan, Spacing, TokenStream, TokenTree};
use rustc_errors::Diag;
use rustc_lexer::{Cursor, FrontmatterAllowed};
use rustc_span::{BytePos, Pos, Span, kw, sym};

use super::Lexer;

/// What a delimited token tree is, as far as island recognition needs to
/// know. Recorded on `Lexer::trust_delim_classes` for every open delimiter
/// on the stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum TrustDelimClass {
    /// The body of `mod name { … }`: items inside are at module item
    /// position, so an island may start there.
    ModuleBody,
    /// A macro invocation's or attribute's token trees (`m!( … )`,
    /// `macro_rules! m { … }`, `macro m { … }`, `#[ … ]`). Nothing inside is
    /// at item position until a macro says so, and a macro must see the
    /// exact tokens the user wrote.
    MacroOrAttr,
    /// Everything else — a function body, a block, a struct body, a struct
    /// literal, generics. Nothing inside is at module item position, but a
    /// `mod name { … }` nested inside is still a real module body.
    Other,
}

/// Why `scan_clean_island_body` could not find the island's closing brace.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum IslandScanError {
    /// End of input with `depth` Lean braces still open; `innermost` is the
    /// byte offset (into the scanned text) of the innermost unclosed `{`, or
    /// `None` when only the island's own brace is open.
    Unclosed { depth: usize, innermost: Option<usize> },
    /// End of input inside a `"…"` string literal opened at `at`.
    UnterminatedString { at: usize },
    /// End of input inside a `r#"…"#` raw string literal opened at `at`.
    UnterminatedRawString { at: usize },
    /// End of input inside a `/- … -/` block comment opened at `at`.
    UnterminatedBlockComment { at: usize },
    /// End of input inside a `«…»` name opened at `at`.
    UnterminatedGuillemets { at: usize },
}

/// Find the `}` that closes a `clean { … }` island.
///
/// `body` is the text immediately AFTER the island's opening `{`. Returns the
/// byte offset into `body` of the matching `}` — `body[offset..].starts_with('}')`
/// holds — or the reason the scan reached end of input first.
///
/// This is a scanner, not a parser: it knows exactly enough Lean lexical
/// structure to tell a structural brace from one inside a comment, string,
/// char literal or `«»` name, and nothing more. It never rejects text — an
/// island full of nonsense with balanced braces scans fine, and the Clean
/// parser then says what is wrong with it.
pub(super) fn scan_clean_island_body(body: &str) -> Result<usize, IslandScanError> {
    let bytes = body.as_bytes();
    let len = bytes.len();
    let mut depth: usize = 1;
    // Offsets of every unclosed `{` seen inside the island, innermost last.
    let mut open_braces: Vec<usize> = Vec::new();
    let mut i = 0usize;
    // The char before `i`, for the identifier-prime and raw-string rules.
    let mut prev: Option<char> = None;

    while i < len {
        let c = char_at(body, i);
        let clen = c.len_utf8();
        match c {
            '-' if bytes.get(i + 1) == Some(&b'-') => {
                // `-- …` line comment: opaque to end of line.
                i = match body[i..].find('\n') {
                    Some(n) => i + n,
                    None => len,
                };
                prev = None;
                continue;
            }
            '/' if bytes.get(i + 1) == Some(&b'-') => {
                // `/- … -/` block comment, NESTED (Lean, unlike C).
                let at = i;
                let mut nest = 1usize;
                i += 2;
                while i < len {
                    if bytes[i] == b'/' && bytes.get(i + 1) == Some(&b'-') {
                        nest += 1;
                        i += 2;
                    } else if bytes[i] == b'-' && bytes.get(i + 1) == Some(&b'/') {
                        nest -= 1;
                        i += 2;
                        if nest == 0 {
                            break;
                        }
                    } else {
                        i += char_at(body, i).len_utf8();
                    }
                }
                if nest != 0 {
                    return Err(IslandScanError::UnterminatedBlockComment { at });
                }
                prev = None;
                continue;
            }
            '"' => {
                // `"…"` string literal; `\` escapes the next char, which also
                // keeps `\"`, `\\` and `\u{…}` opaque.
                let at = i;
                i += 1;
                loop {
                    if i >= len {
                        return Err(IslandScanError::UnterminatedString { at });
                    }
                    match bytes[i] {
                        b'\\' => {
                            i += 1;
                            if i < len {
                                i += char_at(body, i).len_utf8();
                            }
                        }
                        b'"' => {
                            i += 1;
                            break;
                        }
                        _ => i += char_at(body, i).len_utf8(),
                    }
                }
                prev = Some('"');
                continue;
            }
            'r' if !prev.is_some_and(is_lean_ident_char)
                && raw_string_hashes(bytes, i).is_some() =>
            {
                // `r"…"` / `r#"…"#` raw string literal: closes at `"` followed
                // by the same number of `#`.
                let at = i;
                let hashes = raw_string_hashes(bytes, i).unwrap();
                i += 1 + hashes + 1; // `r`, the hashes, the opening `"`
                loop {
                    if i >= len {
                        return Err(IslandScanError::UnterminatedRawString { at });
                    }
                    if bytes[i] == b'"'
                        && i + 1 + hashes <= len
                        && bytes[i + 1..i + 1 + hashes].iter().all(|b| *b == b'#')
                    {
                        i += 1 + hashes;
                        break;
                    }
                    i += char_at(body, i).len_utf8();
                }
                prev = Some('"');
                continue;
            }
            '\'' => {
                // A `'` after an identifier char is part of the identifier
                // (`h'`, `x''`), never a literal. Otherwise `'x'` or an
                // escaped `'\n'`/`'\u{…}'` is a char literal and is opaque —
                // `'{'` and `'}'` must not count as braces. Anything else is
                // a stray quote the Clean parser will refuse; skip one char.
                if prev.is_some_and(is_lean_ident_char) {
                    i += 1;
                    prev = Some('\'');
                    continue;
                }
                if let Some(end) = char_literal_end(body, i) {
                    i = end;
                    prev = Some('\'');
                    continue;
                }
                i += 1;
                prev = Some('\'');
                continue;
            }
            '«' => {
                // `«…»` names may contain anything, braces included.
                let at = i;
                match body[i..].find('»') {
                    Some(n) => i += n + '»'.len_utf8(),
                    None => return Err(IslandScanError::UnterminatedGuillemets { at }),
                }
                prev = Some('»');
                continue;
            }
            '{' => {
                depth += 1;
                open_braces.push(i);
            }
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(i);
                }
                open_braces.pop();
            }
            _ => {}
        }
        i += clen;
        prev = Some(c);
    }

    Err(IslandScanError::Unclosed { depth, innermost: open_braces.last().copied() })
}

fn char_at(s: &str, i: usize) -> char {
    s[i..].chars().next().expect("offset is on a char boundary inside the text")
}

/// Lean identifier characters, for the `'`-is-a-prime rule: letters and
/// digits of any script (`α`, `x₁`), `_`, `'`, the `!`/`?` suffixes, and the
/// closing guillemet of a `«…»` segment.
fn is_lean_ident_char(c: char) -> bool {
    c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?' | '»')
}

/// If `bytes[i..]` starts a raw string literal — `r`, zero or more `#`, `"` —
/// return the number of hashes.
fn raw_string_hashes(bytes: &[u8], i: usize) -> Option<usize> {
    debug_assert_eq!(bytes[i], b'r');
    let mut j = i + 1;
    let mut hashes = 0usize;
    while bytes.get(j) == Some(&b'#') {
        hashes += 1;
        j += 1;
    }
    (bytes.get(j) == Some(&b'"')).then_some(hashes)
}

/// If `body[i..]` (which starts with `'`) is a Lean char literal, return the
/// offset just past its closing `'`.
fn char_literal_end(body: &str, i: usize) -> Option<usize> {
    let bytes = body.as_bytes();
    let mut j = i + 1;
    match bytes.get(j)? {
        b'\\' => {
            j += 1;
            match bytes.get(j)? {
                b'u' => {
                    // `\u{…}`
                    j += 1;
                    if bytes.get(j) != Some(&b'{') {
                        return None;
                    }
                    let close = body[j..].find('}')?;
                    j += close + 1;
                }
                b'x' => j += 3,
                _ => j += char_at(body, j).len_utf8(),
            }
        }
        b'\'' => return None,
        _ => j += char_at(body, j).len_utf8(),
    }
    (bytes.get(j) == Some(&b'\'')).then_some(j + 1)
}

impl<'psess, 'src> Lexer<'psess, 'src> {
    /// Classify the delimited token tree that `self.token` (an open
    /// delimiter) begins, from the token trees already lexed at this level.
    /// Called by `lex_token_trees` before it recurses into the group.
    #[inline]
    pub(super) fn trust_classify_delim(buf: &[TokenTree], open: Delimiter) -> TrustDelimClass {
        let ident_of = |tt: Option<&TokenTree>| match tt {
            Some(TokenTree::Token(Token { kind: token::Ident(name, raw), .. }, _)) => {
                Some((*name, *raw))
            }
            _ => None,
        };
        let is_kind = |tt: Option<&TokenTree>, kind: &token::TokenKind| match tt {
            Some(TokenTree::Token(t, _)) => t.kind == *kind,
            _ => false,
        };
        let is_paren_group = |tt: Option<&TokenTree>| {
            matches!(tt, Some(TokenTree::Delimited(_, _, Delimiter::Parenthesis, _)))
        };
        let n = buf.len();
        let prev = buf.get(n.wrapping_sub(1));
        let prev2 = buf.get(n.wrapping_sub(2));
        let prev3 = buf.get(n.wrapping_sub(3));
        let is_kw = |tt: Option<&TokenTree>, kw: rustc_span::Symbol| {
            ident_of(tt) == Some((kw, IdentKind::Normal))
        };

        // `m!( … )`, `m![ … ]`, `m!{ … }`, `#![ … ]`, `#[ … ]`.
        if is_kind(prev, &token::Bang) || is_kind(prev, &token::Pound) {
            return TrustDelimClass::MacroOrAttr;
        }
        // `macro_rules! name { … }` (any delimiter), `macro name { … }`,
        // `macro name( … )`.
        if ident_of(prev).is_some() && (is_kind(prev2, &token::Bang) || is_kw(prev2, kw::Macro)) {
            return TrustDelimClass::MacroOrAttr;
        }
        // `macro name(args) { body }`.
        if open == Delimiter::Brace
            && is_paren_group(prev)
            && ident_of(prev2).is_some()
            && is_kw(prev3, kw::Macro)
        {
            return TrustDelimClass::MacroOrAttr;
        }
        // `mod name { … }` — `mod` is a reserved keyword, so outside macro
        // token trees (excluded above and by the stack check) this is always
        // a module item.
        if open == Delimiter::Brace && ident_of(prev).is_some() && is_kw(prev2, kw::Mod) {
            return TrustDelimClass::ModuleBody;
        }
        TrustDelimClass::Other
    }

    /// Is `self.token` — an identifier — the `clean` of a `clean { … }`
    /// island at module item position? `buf` holds the token trees already
    /// lexed at this level. Every condition fails closed to "no".
    #[inline]
    pub(super) fn trust_at_clean_island(&self, buf: &[TokenTree]) -> bool {
        if !self.trust_islands_allowed {
            return false;
        }
        if !matches!(self.token.kind, token::Ident(name, IdentKind::Normal) if name == sym::clean) {
            return false;
        }
        // Module item position: innermost delimiter is a module body (or we
        // are at the file's top level), and no macro/attribute token tree
        // encloses us at any depth.
        if !matches!(self.trust_delim_classes.last(), None | Some(TrustDelimClass::ModuleBody)) {
            return false;
        }
        if self.trust_delim_classes.iter().any(|c| *c == TrustDelimClass::MacroOrAttr) {
            return false;
        }
        // The token before `clean` must be one that precedes an ITEM and
        // nothing else at this position: the start of the file or module
        // body, the end of a previous item (`}` or `;`), an attribute
        // (`#[…]`), a doc comment, or a visibility (`pub`, `pub(crate)`).
        // `= clean {`, `-> clean {`, `impl clean {`, `struct clean {` and
        // every other spelling where `clean` is a TYPE or a struct literal
        // are excluded by not being listed.
        let item_position = match buf.last() {
            None => true,
            Some(TokenTree::Delimited(..)) => true,
            Some(TokenTree::Token(t, _)) => {
                t.kind == token::Semi
                    || matches!(t.kind, token::DocComment(..))
                    || t.is_keyword(kw::Pub)
            }
        };
        if !item_position {
            return false;
        }
        // And `{` must be the next token (whitespace and comments between
        // are allowed, exactly as the parser's one-token lookahead sees it).
        self.trust_brace_follows()
    }

    /// Does the next non-trivia token after `self.token` open a brace?
    /// Probed with a fresh sub-lexer so the main cursor is untouched (the
    /// same technique `trust_prime_follows` uses).
    fn trust_brace_follows(&self) -> bool {
        let mut probe = Cursor::new(self.cursor.as_str(), FrontmatterAllowed::No);
        loop {
            let tok = probe.advance_token();
            match tok.kind {
                rustc_lexer::TokenKind::Whitespace
                | rustc_lexer::TokenKind::LineComment { doc_style: None }
                | rustc_lexer::TokenKind::BlockComment { doc_style: None, terminated: true } => {}
                rustc_lexer::TokenKind::OpenBrace => return true,
                _ => return false,
            }
        }
    }

    /// Lex a `clean { … }` island whose `clean` is `self.token`. Returns the
    /// `clean` identifier token (for the caller to push) and the island's
    /// token tree: an EMPTY `Delimited(Brace)` whose open and close spans are
    /// the island's real braces. On return the lexer has moved past the
    /// closing brace and `self.token` is the token after it.
    ///
    /// An island that never closes is an error in the same class as an
    /// unclosed Rust delimiter, and is returned the same way `eof_err` is.
    pub(super) fn trust_lex_clean_island(
        &mut self,
    ) -> Result<((Token, Spacing), TokenTree), Diag<'psess>> {
        // Move past `clean`; `trust_at_clean_island` guaranteed the next
        // token is `{`.
        let clean_tok = self.bump();
        debug_assert_eq!(self.token.kind, token::OpenBrace);
        let open_span = self.token.span;

        // Everything after the `{`, scanned as Lean.
        let body_start = self.pos;
        let rest = self.cursor.as_str();
        let close_off = match scan_clean_island_body(rest) {
            Ok(off) => off,
            Err(err) => return Err(self.trust_unclosed_island_err(open_span, body_start, err)),
        };
        let close_lo = body_start + BytePos::from_usize(close_off);
        let close_span = self.mk_sp(close_lo, close_lo + BytePos(1));

        // Resume ordinary Rust lexing right after the `}`. Nothing lexed
        // before the island can be adjacent to what follows it.
        self.pos = close_lo + BytePos(1);
        self.cursor = Cursor::new(&rest[close_off + 1..], FrontmatterAllowed::No);
        self.trust_last_ident_end = None;
        self.last_lifetime = None;
        // Same bookkeeping `lex_token_tree_open_delim` does for a real brace
        // pair, so mismatched-delimiter diagnostics elsewhere in the file can
        // still use these braces as a matched pair.
        self.diag_info.matching_block_spans.push((open_span, close_span));
        let close_spacing = self.bump_minimal();

        let dspan = DelimSpan::from_pair(open_span, close_span);
        let spacing = DelimSpacing::new(Spacing::Alone, close_spacing);
        Ok((
            clean_tok,
            TokenTree::Delimited(dspan, spacing, Delimiter::Brace, TokenStream::new(vec![])),
        ))
    }

    /// Ruling v7/D3: the refusal names where the scanner stopped and what
    /// closes it.
    fn trust_unclosed_island_err(
        &self,
        open_span: Span,
        body_start: BytePos,
        err: IslandScanError,
    ) -> Diag<'psess> {
        let at = |off: usize| {
            let lo = body_start + BytePos::from_usize(off);
            self.mk_sp(lo, lo + BytePos(1))
        };
        let mut diag = self.dcx().struct_span_err(
            open_span,
            "this `clean { … }` island is never closed: the file ended before its `}`",
        );
        diag.span_label(open_span, "island opened here");
        match err {
            IslandScanError::Unclosed { depth, innermost } => {
                if let Some(off) = innermost {
                    diag.span_label(
                        at(off),
                        format!(
                            "this Lean `{{` is still open at end of file ({} unclosed in total)",
                            depth
                        ),
                    );
                }
                diag.note(
                    "the island body is scanned as Clean (Lean) text: `{ … }` inside it must \
                     balance, and only a `}` outside every Lean comment, string, char literal \
                     and `«…»` name closes the island",
                );
            }
            IslandScanError::UnterminatedString { at: off } => {
                diag.span_label(at(off), "this Lean string literal is never closed");
                diag.note(
                    "a `\"` inside the island opens a Lean string; `\\\"` is an escaped quote",
                );
            }
            IslandScanError::UnterminatedRawString { at: off } => {
                diag.span_label(at(off), "this Lean raw string literal is never closed");
                diag.note(
                    "an `r#\"…\"#` raw string closes only at `\"` followed by the same hashes",
                );
            }
            IslandScanError::UnterminatedBlockComment { at: off } => {
                diag.span_label(at(off), "this Lean block comment is never closed");
                diag.note("Lean block comments nest: every `/-` needs its own `-/`");
            }
            IslandScanError::UnterminatedGuillemets { at: off } => {
                diag.span_label(at(off), "this `«…»` name is never closed");
            }
        }
        diag.help(
            "options: close the construct the label points at; or, if the text was meant to \
             be Rust, drop the `clean` keyword so the braces lex as ordinary Rust",
        );
        diag
    }
}

#[cfg(test)]
mod tests;
