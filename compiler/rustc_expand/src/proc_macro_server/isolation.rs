//! Trust (D21): compiler-owned token values for the existing B1 protocol.
//!
//! `launch.rs` starts the sandboxed worker and drives the dispatcher for each
//! expansion under `-Ztrust-proc-macro-isolation`; `worker.rs` is the worker's
//! entry. Neither decides which lanes admit a proc-macro dependency: that is
//! Targo's and the crate loader's PM-1 boundary. B1 has
//! no representation for forced keywords or error-guaranteed literals; those
//! refuse rather than lose meaning. Handles never contain raw span/hygiene IDs.

use std::mem::size_of;

use rustc_ast::token as tk;
use rustc_ast::tokenstream::{self, TokenStream};
use rustc_data_structures::fx::FxHashMap;
use rustc_parse::lexer::nfc_normalize;
use rustc_proc_macro::Delimiter;
use rustc_proc_macro::bridge::{DelimSpan, Group, Ident, IdentKind, LitKind, Literal, Punct};
use rustc_session::parse::ParseSess;
use rustc_span::{Span, Symbol};
use trust_process_isolation::{
    Budget, Charge, Error, Handle, HandleKind, HandleTable, HandleUse, Tree, UseMode,
};

use super::{FromInternal, TokenTree, parse_literal, token_tree_to_internal};

type NativeTree = TokenTree<TokenStream, Span, Symbol>;

#[derive(Debug)]
enum OwnedValue {
    Stream(TokenStream),
    Span(Span),
}

pub(crate) struct TokenAdapter {
    values: HandleTable<OwnedValue>,
    budget: Budget,
    /// Where each stored span lives, so interning one token's span does not
    /// scan every handle of the expansion. An index only: `values` decides.
    spans: FxHashMap<Span, Handle>,
}

impl TokenAdapter {
    pub(crate) fn new(invocation: u64, budget: Budget) -> Result<Self, Error> {
        Ok(Self {
            values: HandleTable::new(invocation, budget.clone())?,
            budget,
            spans: FxHashMap::default(),
        })
    }

    fn finish<T>(&mut self, result: Result<T, Error>) -> Result<T, Error> {
        result.map_err(|error| {
            self.budget.refuse(error.clone());
            self.clear();
            error
        })
    }

    pub(crate) fn store_stream(&mut self, stream: TokenStream) -> Result<Handle, Error> {
        let result = self
            .preflight(&stream, 0)
            .and_then(|()| self.values.insert(HandleKind::Stream, OwnedValue::Stream(stream)));
        self.finish(result)
    }

    pub(crate) fn store_span(&mut self, span: Span) -> Result<Handle, Error> {
        // Trust: native proc_macro interns Span by Eq/Hash. Preserve that
        // identity across B1 responses without exposing raw span/hygiene data.
        // Only live immutable Span values are reused; streams remain owned.
        let result = (|| {
            if let Some(&handle) = self.spans.get(&span) {
                // The table is the authority: an indexed handle is reused only
                // while it still names this live span.
                if matches!(self.values.get(handle), Ok(OwnedValue::Span(live)) if *live == span) {
                    self.budget.charge(Charge { work: 1, ..Charge::default() })?;
                    return Ok(handle);
                }
            }
            let handle = self.values.insert(HandleKind::Span, OwnedValue::Span(span))?;
            self.spans.insert(span, handle);
            Ok(handle)
        })();
        self.finish(result)
    }

    /// Drop every value. Handles issued so far name nothing afterwards.
    pub(crate) fn clear(&mut self) {
        self.values.clear();
        self.spans.clear();
    }

    fn span(&self, handle: Handle) -> Result<Span, Error> {
        match self.values.get(handle)? {
            OwnedValue::Span(span) if handle.kind == HandleKind::Span => Ok(*span),
            _ => Err(Error::Handle("expected span")),
        }
    }

    fn stream(&self, handle: Handle) -> Result<TokenStream, Error> {
        match self.values.get(handle)? {
            OwnedValue::Stream(stream) if handle.kind == HandleKind::Stream => Ok(stream.clone()),
            _ => Err(Error::Handle("expected stream")),
        }
    }

    /// The lookup and definition-site context belong to the compiler, not the
    /// worker. The eventual dispatcher must capture its own macro crate here.
    pub(crate) fn recover_quoted_span(
        &mut self,
        index: u64,
        def_site: Span,
        lookup: impl FnOnce(usize) -> Option<Span>,
    ) -> Result<Handle, Error> {
        let result = (|| {
            self.budget.charge(Charge { work: 1, ..Charge::default() })?;
            let index =
                usize::try_from(index).map_err(|_| Error::InvalidWire("quoted span index"))?;
            let span = lookup(index).ok_or(Error::InvalidWire("quoted span index"))?;
            self.store_span(span.with_ctxt(def_site.ctxt()))
        })();
        self.finish(result)
    }

    /// Mirrors native `ts_into_trees`, including its documented normalization
    /// of operators, doc comments and invisible metavariable groups.
    pub(crate) fn export_stream(&mut self, handle: Handle) -> Result<Vec<Tree>, Error> {
        let result = (|| {
            let stream = self.stream(handle)?;
            self.preflight(&stream, 0)?;
            let native = Vec::<NativeTree>::from_internal(stream);
            let mut output = self.reserve(native.len())?;
            for tree in native {
                output.push(self.export_tree(tree)?);
            }
            Ok(output)
        })();
        self.finish(result)
    }

    fn export_tree(&mut self, tree: NativeTree) -> Result<Tree, Error> {
        Ok(match tree {
            TokenTree::Group(Group { delimiter, stream, span }) => Tree::Group {
                delimiter: match delimiter {
                    Delimiter::Parenthesis => 0,
                    Delimiter::Brace => 1,
                    Delimiter::Bracket => 2,
                    Delimiter::None => 3,
                },
                stream: stream
                    .map(|s| self.values.insert(HandleKind::Stream, OwnedValue::Stream(s)))
                    .transpose()?,
                spans: [
                    self.store_span(span.open)?,
                    self.store_span(span.close)?,
                    self.store_span(span.entire)?,
                ],
            },
            TokenTree::Punct(Punct { ch, joint, span }) => {
                Tree::Punct { ch, joint, span: self.store_span(span)? }
            }
            TokenTree::Ident(Ident { sym, kind, span }) => {
                if kind == IdentKind::ForcedKeyword {
                    return Err(Error::InvalidWire("B1 cannot represent forced keywords"));
                }
                self.charge_text(sym.as_str())?;
                Tree::Ident {
                    symbol: sym.as_str().to_owned(),
                    is_raw: kind == IdentKind::Raw,
                    span: self.store_span(span)?,
                }
            }
            TokenTree::Literal(Literal { kind, symbol, suffix, span }) => {
                let (kind, raw_hashes) = literal_kind(kind)?;
                self.charge_text(symbol.as_str())?;
                if let Some(suffix) = suffix {
                    self.charge_text(suffix.as_str())?;
                }
                Tree::Literal(trust_process_isolation::Literal {
                    kind,
                    raw_hashes,
                    symbol: symbol.as_str().to_owned(),
                    suffix: suffix.map(|s| s.as_str().to_owned()),
                    span: self.store_span(span)?,
                })
            }
        })
    }

    /// Validate all semantics and all handles before consuming any group
    /// stream. A later invalid tree cannot partially consume an earlier one.
    pub(crate) fn import_trees(
        &mut self,
        psess: &ParseSess,
        trees: &[Tree],
    ) -> Result<TokenStream, Error> {
        let result = (|| {
            let mut native = self.reserve(trees.len())?;
            let uses_len = trees.len().checked_mul(4).ok_or(Error::Overflow)?;
            let mut uses = self.reserve(uses_len)?;
            for tree in trees {
                self.budget.charge(Charge { values: 1, work: 1, ..Charge::default() })?;
                native.push(self.import_tree(psess, tree, &mut uses)?);
            }
            // Also rejects duplicate consuming aliases across separate trees.
            let _consumed = self.values.consume(&uses)?;
            let count = native.len().checked_mul(2).ok_or(Error::Overflow)?;
            let mut tokens = self.reserve(count)?;
            for tree in native {
                tokens.extend(token_tree_to_internal(tree, psess));
            }
            self.budget.check()?;
            Ok(TokenStream::new(tokens))
        })();
        self.finish(result)
    }

    fn import_tree(
        &self,
        psess: &ParseSess,
        tree: &Tree,
        uses: &mut Vec<HandleUse>,
    ) -> Result<NativeTree, Error> {
        let mut span = |h| {
            let span = self.span(h)?;
            uses.push(HandleUse { handle: h, mode: UseMode::Borrow });
            Ok::<_, Error>(span)
        };
        Ok(match tree {
            Tree::Group { delimiter, stream, spans } => {
                let delimiter = match delimiter {
                    0 => Delimiter::Parenthesis,
                    1 => Delimiter::Brace,
                    2 => Delimiter::Bracket,
                    3 => Delimiter::None,
                    _ => return Err(Error::InvalidWire("delimiter")),
                };
                let spans = DelimSpan {
                    open: span(spans[0])?,
                    close: span(spans[1])?,
                    entire: span(spans[2])?,
                };
                let stream = stream
                    .map(|h| {
                        let stream = self.stream(h)?;
                        self.preflight(&stream, 1)?;
                        uses.push(HandleUse { handle: h, mode: UseMode::Consume });
                        Ok::<_, Error>(stream)
                    })
                    .transpose()?;
                TokenTree::Group(Group { delimiter, stream, span: spans })
            }
            Tree::Punct { ch, joint, span: h } => {
                if !b"=<>!~+-*/%^&|@.,;:#$?'".contains(ch) {
                    return Err(Error::InvalidWire("punctuation"));
                }
                TokenTree::Punct(Punct { ch: *ch, joint: *joint, span: span(*h)? })
            }
            Tree::Ident { symbol, is_raw, span: h } => {
                self.charge_text(symbol)?;
                let sym = nfc_normalize(symbol);
                if (sym.as_str() != "$crate" && !rustc_lexer::is_ident(sym.as_str()))
                    || (*is_raw && !sym.can_be_raw())
                {
                    return Err(Error::InvalidWire("identifier"));
                }
                TokenTree::Ident(Ident {
                    sym,
                    kind: if *is_raw { IdentKind::Raw } else { IdentKind::Normal },
                    span: span(*h)?,
                })
            }
            Tree::Literal(literal) => {
                let span = span(literal.span)?;
                TokenTree::Literal(self.import_literal(psess, literal, span)?)
            }
        })
    }

    fn import_literal(
        &self,
        psess: &ParseSess,
        literal: &trust_process_isolation::Literal,
        span: Span,
    ) -> Result<Literal<Span, Symbol>, Error> {
        // Reserve the parser's per-literal bookkeeping as well as its strings.
        // This is adapter accounting, not an RSS or hard-latency guarantee.
        self.charge_storage::<u8>(4096)?;
        self.charge_text(&literal.symbol)?;
        if let Some(suffix) = &literal.suffix {
            self.charge_text(suffix)?;
        }
        let hashes = usize::from(literal.raw_hashes);
        let (kind, prefix, quote) = match literal.kind {
            0 => (LitKind::Byte, "b", "'"),
            1 => (LitKind::Char, "", "'"),
            2 => (LitKind::Integer, "", ""),
            3 => (LitKind::Float, "", ""),
            4 => (LitKind::Str, "", "\""),
            5 => (LitKind::StrRaw(literal.raw_hashes), "r", "\""),
            6 => (LitKind::ByteStr, "b", "\""),
            7 => (LitKind::ByteStrRaw(literal.raw_hashes), "br", "\""),
            8 => (LitKind::CStr, "c", "\""),
            9 => (LitKind::CStrRaw(literal.raw_hashes), "cr", "\""),
            _ => return Err(Error::InvalidWire("literal kind")),
        };
        if !matches!(literal.kind, 5 | 7 | 9) && hashes != 0 {
            return Err(Error::InvalidWire("literal raw hashes"));
        }
        // Includes parser token storage, quote/hash delimiters and strings.
        self.charge_text(&"#".repeat(hashes * 2 + 8))?;
        let marks = "#".repeat(hashes);
        let text = format!(
            "{prefix}{marks}{quote}{}{quote}{marks}{}",
            literal.symbol,
            literal.suffix.as_deref().unwrap_or("")
        );
        validate_literal_lexically(&text, literal.suffix.as_deref())?;
        let parsed = parse_literal(psess, &text, span)
            .map_err(|_| Error::InvalidWire("literal spelling"))?;
        // Native suffixed float constructors use `1f64` with Float kind even
        // though the lexer represents that spelling as an Integer token.
        let integral_float = kind == LitKind::Float
            && parsed.kind == LitKind::Integer
            && matches!(literal.suffix.as_deref(), Some("f32" | "f64"))
            && literal
                .symbol
                .strip_prefix('-')
                .unwrap_or(&literal.symbol)
                .chars()
                .all(|c| c.is_ascii_digit() || c == '_');
        if (parsed.kind != kind && !integral_float)
            || parsed.symbol.as_str() != literal.symbol
            || parsed.suffix.as_ref().map(|s| s.as_str()) != literal.suffix.as_deref()
        {
            return Err(Error::InvalidWire("literal spelling/kind/suffix"));
        }
        Ok(Literal { kind, symbol: parsed.symbol, suffix: parsed.suffix, span })
    }

    fn reserve<T>(&self, count: usize) -> Result<Vec<T>, Error> {
        self.charge_storage::<T>(count)?;
        let mut result = Vec::new();
        result.try_reserve_exact(count).map_err(|_| Error::Allocation)?;
        self.charge_storage::<T>(result.capacity().saturating_sub(count))?;
        Ok(result)
    }

    fn charge_storage<T>(&self, count: usize) -> Result<(), Error> {
        let bytes = count.checked_mul(size_of::<T>()).ok_or(Error::Overflow)?;
        self.budget.charge(Charge { allocation_bytes: bytes as u64, ..Charge::default() })
    }

    fn charge_text(&self, text: &str) -> Result<(), Error> {
        let bytes = text.len().checked_mul(32).ok_or(Error::Overflow)?;
        self.budget.charge(Charge {
            allocation_bytes: bytes as u64,
            work: bytes as u64,
            ..Charge::default()
        })
    }

    fn preflight(&self, stream: &TokenStream, depth: u16) -> Result<(), Error> {
        self.budget.depth(depth)?;
        // Native conversion can split operators/lifetimes and expand a doc
        // comment into an attribute. Preprice replacement vectors and compiler
        // token storage, not just the B1 frame's inline allocation.
        self.charge_storage::<(NativeTree, Tree, tokenstream::TokenTree)>(
            stream.len().max(1).checked_mul(32).ok_or(Error::Overflow)?,
        )?;
        for tree in stream.iter() {
            self.budget.charge(Charge { values: 1, work: 1, ..Charge::default() })?;
            match tree {
                tokenstream::TokenTree::Delimited(_, _, _, stream) => {
                    self.preflight(stream, depth.checked_add(1).ok_or(Error::Overflow)?)?;
                }
                tokenstream::TokenTree::Token(token, _) => match token.kind {
                    tk::Ident(_, tk::IdentKind::ForcedKeyword)
                    | tk::NtIdent(_, tk::IdentKind::ForcedKeyword)
                    | tk::Lifetime(_, tk::IdentKind::ForcedKeyword)
                    | tk::NtLifetime(_, tk::IdentKind::ForcedKeyword) => {
                        return Err(Error::InvalidWire("B1 cannot represent forced keywords"));
                    }
                    tk::Literal(lit) => {
                        if lit.kind == tk::Bool {
                            return Err(Error::InvalidWire(
                                "boolean is an identifier, not a literal",
                            ));
                        }
                        literal_kind(LitKind::from_internal(lit.kind))?;
                        self.charge_text(lit.symbol.as_str())?;
                        if let Some(suffix) = lit.suffix {
                            self.charge_text(suffix.as_str())?;
                        }
                    }
                    tk::Ident(s, _) | tk::Lifetime(s, _) | tk::DocComment(_, _, s) => {
                        self.charge_text(s.as_str())?
                    }
                    tk::NtIdent(i, _) | tk::NtLifetime(i, _) => {
                        self.charge_text(i.name.as_str())?
                    }
                    tk::OpenParen
                    | tk::CloseParen
                    | tk::OpenBrace
                    | tk::CloseBrace
                    | tk::OpenBracket
                    | tk::CloseBracket
                    | tk::OpenInvisible(_)
                    | tk::CloseInvisible(_)
                    | tk::Eof => return Err(Error::InvalidWire("non-tree token")),
                    _ => {}
                },
            }
        }
        self.budget.check()
    }
}

// A nonrecursive lexer pass must precede the full parser: arbitrary worker
// text such as thousands of opening delimiters must never reach its token-tree
// recursion. This pass accepts only one complete literal (optionally negative).
fn validate_literal_lexically(text: &str, suffix: Option<&str>) -> Result<(), Error> {
    use rustc_lexer::{LiteralKind as L, TokenKind as T};
    if text.len() > u32::MAX as usize {
        return Err(Error::InvalidWire("literal length"));
    }
    let mut tokens = rustc_lexer::tokenize(text, rustc_lexer::FrontmatterAllowed::No);
    let first = tokens.next().ok_or(Error::InvalidWire("empty literal"))?;
    let (offset, token) = if first.kind == T::Minus {
        (1, tokens.next().ok_or(Error::InvalidWire("missing negative literal"))?)
    } else {
        (0, first)
    };
    let T::Literal { kind, suffix_start } = token.kind else {
        return Err(Error::InvalidWire("literal token"));
    };
    let complete = match kind {
        L::Int { empty_int, .. } => !empty_int,
        L::Float { empty_exponent, .. } => !empty_exponent,
        L::Char { terminated }
        | L::Byte { terminated }
        | L::Str { terminated }
        | L::ByteStr { terminated }
        | L::CStr { terminated } => terminated,
        L::RawStr { n_hashes } | L::RawByteStr { n_hashes } | L::RawCStr { n_hashes } => {
            n_hashes.is_some()
        }
    };
    if !complete
        || offset + token.len as usize != text.len()
        || tokens.next().is_some()
        || text.get(offset + suffix_start as usize..) != Some(suffix.unwrap_or(""))
    {
        return Err(Error::InvalidWire("literal token boundary"));
    }
    Ok(())
}

fn literal_kind(kind: LitKind) -> Result<(u8, u8), Error> {
    Ok(match kind {
        LitKind::Byte => (0, 0),
        LitKind::Char => (1, 0),
        LitKind::Integer => (2, 0),
        LitKind::Float => (3, 0),
        LitKind::Str => (4, 0),
        LitKind::StrRaw(n) => (5, n),
        LitKind::ByteStr => (6, 0),
        LitKind::ByteStrRaw(n) => (7, n),
        LitKind::CStr => (8, 0),
        LitKind::CStrRaw(n) => (9, n),
        LitKind::ErrWithGuar => return Err(Error::InvalidWire("error-guaranteed literal")),
    })
}

pub(crate) mod dispatch;
pub(crate) mod launch;
pub(crate) mod worker;

#[cfg(test)]
mod tests;
