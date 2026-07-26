// trust-js-parse: the lexer — ECMAScript 2025 lexical grammar over Unicode
// code points. Goal-symbol sensitivity (InputElementDiv vs InputElementRegExp
// vs template continuation) is handled by parser-driven re-lexing: the default
// goal is Div, and the parser rewinds + re-lexes when it expects a regex
// literal or a template middle/tail.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::unicode_id::{ID_CONTINUE, ID_START};

/// A lex/parse failure. `Early` is a spec-mandated SyntaxError; `Unsupported`
/// is a sound refusal (out-of-slice grammar such as Annex B, or a surface we
/// do not yet classify with confidence).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fail {
    Early(String),
    Unsupported(String),
}

impl Fail {
    pub fn early(msg: impl Into<String>) -> Self {
        Fail::Early(msg.into())
    }
    pub fn unsupported(msg: impl Into<String>) -> Self {
        Fail::Unsupported(msg.into())
    }
}

pub type LexResult<T> = Result<T, Fail>;

/// Punctuators (and the punctuator-shaped tokens `/` `/=` that may be
/// re-lexed as a regex literal by the parser).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum P {
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Dot,
    Ellipsis,
    Semi,
    Comma,
    Lt,
    Gt,
    Le,
    Ge,
    EqEq,
    NotEq,
    EqEqEq,
    NotEqEq,
    Plus,
    Minus,
    Star,
    Percent,
    StarStar,
    PlusPlus,
    MinusMinus,
    Shl,
    Shr,
    UShr,
    Amp,
    Pipe,
    Caret,
    Bang,
    Tilde,
    AmpAmp,
    PipePipe,
    Question,
    QuestionQuestion,
    QuestionDot,
    Colon,
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
    PercentEq,
    StarStarEq,
    ShlEq,
    ShrEq,
    UShrEq,
    AmpEq,
    PipeEq,
    CaretEq,
    AmpAmpEq,
    PipePipeEq,
    QuestionQuestionEq,
    Arrow,
    Slash,
    SlashEq,
}

/// Numeric literal classification flags needed for early errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct NumFlags {
    /// LegacyOctalIntegerLiteral (e.g. `012`) — Syntax Error in strict code.
    pub legacy_octal: bool,
    /// NonOctalDecimalIntegerLiteral (e.g. `08`) — Syntax Error in strict code.
    pub non_octal_decimal: bool,
    /// BigInt literal suffix `n`.
    pub bigint: bool,
}

/// String-literal flags needed for early errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct StrFlags {
    /// Contains a LegacyOctalEscapeSequence — Syntax Error in strict code.
    pub legacy_octal_escape: bool,
    /// Contains `\8` or `\9` — Syntax Error in strict code.
    pub non_octal_escape: bool,
    /// Contains any escape or line continuation (a directive must be the
    /// exact unescaped sequence).
    pub any_escape: bool,
}

/// Template-literal piece kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TplKind {
    /// `` `...` `` — complete, no substitutions.
    NoSub,
    /// `` `...${ `` — head of a substitution template.
    Head,
    /// `}...${` — middle piece (only produced by `relex_template_continue`).
    Middle,
    /// `` }...` `` — tail piece (only produced by `relex_template_continue`).
    Tail,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Eof,
    /// IdentifierName (including all keywords — the parser classifies
    /// contextually since reservedness depends on mode/context).
    Ident(String),
    /// `#name`
    PrivateIdent(String),
    Num {
        raw: String,
        flags: NumFlags,
    },
    Str {
        /// Raw source between the quotes.
        raw: String,
        flags: StrFlags,
    },
    Template {
        kind: TplKind,
        /// Raw source of the piece (between the delimiters).
        raw: String,
        /// The cooked value failed (invalid escape) — allowed only in tagged
        /// templates.
        invalid_escape: bool,
        /// Contains an octal / \8 \9 escape (always an error when untagged,
        /// in any mode).
        octal_escape: bool,
    },
    /// Only produced by `relex_regex`.
    Regex {
        pattern: String,
        flags: String,
    },
    Punct(P),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    /// Code-point index of the first code point of the token.
    pub start: usize,
    /// Code-point index one past the last code point.
    pub end: usize,
    /// A LineTerminator (or a comment containing one) precedes this token.
    pub newline_before: bool,
    /// An identifier that contained a `\u` escape (escaped keywords are not
    /// keywords; escaped reserved words are early errors as identifiers).
    pub had_escape: bool,
}

impl Token {
    pub fn is_punct(&self, p: P) -> bool {
        self.kind == TokenKind::Punct(p)
    }
    /// Unescaped identifier equal to `s` (keyword matcher).
    pub fn is_kw(&self, s: &str) -> bool {
        !self.had_escape && matches!(&self.kind, TokenKind::Ident(v) if v == s)
    }
    /// Identifier name regardless of escapes.
    pub fn ident_name(&self) -> Option<&str> {
        match &self.kind {
            TokenKind::Ident(v) => Some(v),
            _ => None,
        }
    }
}

fn is_line_terminator(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

fn is_whitespace(c: char) -> bool {
    matches!(
        c,
        '\u{9}' | '\u{B}' | '\u{C}' | '\u{20}' | '\u{A0}' | '\u{FEFF}'
    ) || matches!(
        c,
        '\u{1680}' | '\u{2000}'..='\u{200A}' | '\u{202F}' | '\u{205F}' | '\u{3000}'
    )
}

fn in_table(table: &[(u32, u32)], c: char) -> bool {
    let cp = c as u32;
    table
        .binary_search_by(|&(lo, hi)| {
            if hi < cp {
                std::cmp::Ordering::Less
            } else if lo > cp {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        })
        .is_ok()
}

pub fn is_id_start(c: char) -> bool {
    c == '$' || c == '_' || in_table(ID_START, c)
}

pub fn is_id_continue(c: char) -> bool {
    c == '$' || c == '_' || c == '\u{200C}' || c == '\u{200D}' || in_table(ID_CONTINUE, c)
}

pub struct Lexer {
    src: Vec<char>,
    pos: usize,
}

impl Lexer {
    pub fn new(source: &str) -> Self {
        Lexer {
            src: source.chars().collect(),
            pos: 0,
        }
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    /// Rewind to an absolute code-point position (used for re-lexing).
    pub fn seek(&mut self, pos: usize) {
        self.pos = pos;
    }

    fn peek(&self) -> Option<char> {
        self.src.get(self.pos).copied()
    }

    fn peek_at(&self, off: usize) -> Option<char> {
        self.src.get(self.pos + off).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    /// Skip the hashbang comment if present at position 0.
    pub fn skip_hashbang(&mut self) {
        if self.pos == 0 && self.peek() == Some('#') && self.peek_at(1) == Some('!') {
            while let Some(c) = self.peek() {
                if is_line_terminator(c) {
                    break;
                }
                self.pos += 1;
            }
        }
    }

    /// Skip whitespace + comments. Returns whether a line terminator was
    /// crossed. HTML-like comments (`<!--`, line-start `-->`) are Annex B and
    /// out of slice: refuse.
    fn skip_trivia(&mut self) -> LexResult<bool> {
        let mut newline = false;
        loop {
            match self.peek() {
                Some(c) if is_whitespace(c) => {
                    self.pos += 1;
                }
                Some(c) if is_line_terminator(c) => {
                    newline = true;
                    self.pos += 1;
                }
                Some('/') if self.peek_at(1) == Some('/') => {
                    self.pos += 2;
                    while let Some(c) = self.peek() {
                        if is_line_terminator(c) {
                            break;
                        }
                        self.pos += 1;
                    }
                }
                Some('/') if self.peek_at(1) == Some('*') => {
                    self.pos += 2;
                    let mut closed = false;
                    while let Some(c) = self.bump() {
                        if is_line_terminator(c) {
                            newline = true;
                        }
                        if c == '*' && self.peek() == Some('/') {
                            self.pos += 1;
                            closed = true;
                            break;
                        }
                    }
                    if !closed {
                        return Err(Fail::early("unterminated block comment"));
                    }
                }
                Some('<')
                    if self.peek_at(1) == Some('!')
                        && self.peek_at(2) == Some('-')
                        && self.peek_at(3) == Some('-') =>
                {
                    return Err(Fail::unsupported(
                        "annexB html-open-comment <!-- (out of slice)",
                    ));
                }
                Some('-')
                    if self.peek_at(1) == Some('-')
                        && self.peek_at(2) == Some('>')
                        && (newline || self.at_line_start()) =>
                {
                    return Err(Fail::unsupported(
                        "annexB html-close-comment --> (out of slice)",
                    ));
                }
                _ => break,
            }
        }
        Ok(newline)
    }

    /// True when only whitespace/comments precede `self.pos` on its line.
    fn at_line_start(&self) -> bool {
        let mut i = self.pos;
        while i > 0 {
            let c = self.src[i - 1];
            if is_line_terminator(c) {
                return true;
            }
            if is_whitespace(c) {
                i -= 1;
                continue;
            }
            return false;
        }
        true
    }

    /// Lex the next token with the Div goal (`/` and `/=` are punctuators).
    pub fn next_token(&mut self) -> LexResult<Token> {
        let newline_before = self.skip_trivia()?;
        let start = self.pos;
        let mut had_escape = false;
        let kind = match self.peek() {
            None => TokenKind::Eof,
            Some(c) if is_id_start(c) => {
                let name = self.lex_identifier_name(&mut had_escape)?;
                TokenKind::Ident(name)
            }
            Some('\\') => {
                let name = self.lex_identifier_name(&mut had_escape)?;
                TokenKind::Ident(name)
            }
            Some('#') => {
                self.pos += 1;
                match self.peek() {
                    Some(c) if is_id_start(c) || c == '\\' => {
                        let name = self.lex_identifier_name(&mut had_escape)?;
                        TokenKind::PrivateIdent(name)
                    }
                    _ => return Err(Fail::early("lone '#' is not a valid token")),
                }
            }
            Some(c) if c.is_ascii_digit() => self.lex_number()?,
            Some('.') if self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) => {
                self.lex_number()?
            }
            Some('"') | Some('\'') => self.lex_string()?,
            Some('`') => self.lex_template(true)?,
            Some(_) => self.lex_punct()?,
        };
        Ok(Token {
            kind,
            start,
            end: self.pos,
            newline_before,
            had_escape,
        })
    }

    fn lex_unicode_escape_in_ident(&mut self) -> LexResult<char> {
        // At the backslash.
        if self.peek() != Some('\\') || self.peek_at(1) != Some('u') {
            return Err(Fail::early("invalid escape in identifier"));
        }
        self.pos += 2;
        let cp = self.lex_unicode_escape_value()?;
        char::from_u32(cp).ok_or_else(|| Fail::early("invalid code point in identifier escape"))
    }

    /// After `\u` has been consumed: `hhhh` or `{h+}` — returns scalar value.
    fn lex_unicode_escape_value(&mut self) -> LexResult<u32> {
        if self.peek() == Some('{') {
            self.pos += 1;
            let mut v: u32 = 0;
            let mut any = false;
            while let Some(c) = self.peek() {
                if let Some(d) = c.to_digit(16) {
                    any = true;
                    v = v.saturating_mul(16).saturating_add(d);
                    if v > 0x10FFFF {
                        return Err(Fail::early("unicode escape out of range"));
                    }
                    self.pos += 1;
                } else {
                    break;
                }
            }
            if !any || self.peek() != Some('}') {
                return Err(Fail::early("malformed \\u{...} escape"));
            }
            self.pos += 1;
            Ok(v)
        } else {
            let mut v: u32 = 0;
            for _ in 0..4 {
                match self.peek().and_then(|c| c.to_digit(16)) {
                    Some(d) => {
                        v = v * 16 + d;
                        self.pos += 1;
                    }
                    None => return Err(Fail::early("malformed \\uXXXX escape")),
                }
            }
            Ok(v)
        }
    }

    fn lex_identifier_name(&mut self, had_escape: &mut bool) -> LexResult<String> {
        let mut name = String::new();
        // First code point.
        match self.peek() {
            Some('\\') => {
                *had_escape = true;
                let c = self.lex_unicode_escape_in_ident()?;
                if !is_id_start(c) {
                    return Err(Fail::early("escaped code point is not ID_Start"));
                }
                name.push(c);
            }
            Some(c) if is_id_start(c) => {
                name.push(c);
                self.pos += 1;
            }
            _ => return Err(Fail::early("expected identifier")),
        }
        loop {
            match self.peek() {
                Some('\\') => {
                    *had_escape = true;
                    let c = self.lex_unicode_escape_in_ident()?;
                    if !is_id_continue(c) {
                        return Err(Fail::early("escaped code point is not ID_Continue"));
                    }
                    name.push(c);
                }
                Some(c) if is_id_continue(c) => {
                    name.push(c);
                    self.pos += 1;
                }
                _ => break,
            }
        }
        Ok(name)
    }

    fn lex_number(&mut self) -> LexResult<TokenKind> {
        let start = self.pos;
        let mut flags = NumFlags::default();
        let first = self.peek().unwrap();
        if first == '0'
            && matches!(
                self.peek_at(1),
                Some('x') | Some('X') | Some('o') | Some('O') | Some('b') | Some('B')
            )
        {
            let base_ch = self.peek_at(1).unwrap().to_ascii_lowercase();
            self.pos += 2;
            let radix = match base_ch {
                'x' => 16,
                'o' => 8,
                _ => 2,
            };
            let mut any = false;
            let mut last_sep = false;
            while let Some(c) = self.peek() {
                if c == '_' {
                    if !any || last_sep {
                        return Err(Fail::early("misplaced numeric separator"));
                    }
                    last_sep = true;
                    self.pos += 1;
                } else if c.to_digit(radix).is_some() {
                    any = true;
                    last_sep = false;
                    self.pos += 1;
                } else {
                    break;
                }
            }
            if !any || last_sep {
                return Err(Fail::early("malformed radix numeric literal"));
            }
            if self.peek() == Some('n') {
                flags.bigint = true;
                self.pos += 1;
            }
        } else if first == '0' && self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) {
            // LegacyOctalIntegerLiteral or NonOctalDecimalIntegerLiteral.
            // Separators are not allowed in these.
            self.pos += 1;
            let mut non_octal = false;
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    if c == '8' || c == '9' {
                        non_octal = true;
                    }
                    self.pos += 1;
                } else {
                    break;
                }
            }
            if non_octal {
                flags.non_octal_decimal = true;
                // May continue as decimal: `08.5`, `09e2` are legal sloppy.
                if self.peek() == Some('.') {
                    self.pos += 1;
                    self.lex_decimal_digits(false)?;
                }
                self.lex_exponent()?;
            } else {
                flags.legacy_octal = true;
            }
            if self.peek() == Some('n') {
                return Err(Fail::early("bigint suffix on legacy octal literal"));
            }
        } else {
            // DecimalLiteral.
            let mut int_digits = false;
            if first != '.' {
                int_digits = true;
                if first == '0' && self.peek_at(1) == Some('_') {
                    return Err(Fail::early("numeric separator after leading zero"));
                }
                self.lex_decimal_digits(true)?;
                if self.peek() == Some('n') {
                    // DecimalBigInteger: no leading zero unless just `0`.
                    let text: String = self.src[start..self.pos].iter().collect();
                    if text.len() > 1 && text.starts_with('0') {
                        return Err(Fail::early("bigint with leading zero"));
                    }
                    self.pos += 1;
                    flags.bigint = true;
                    let raw: String = self.src[start..self.pos].iter().collect();
                    self.check_no_ident_after_number()?;
                    return Ok(TokenKind::Num { raw, flags });
                }
            }
            if self.peek() == Some('.') {
                self.pos += 1;
                if self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    self.lex_decimal_digits(false)?;
                } else if !int_digits {
                    return Err(Fail::early("malformed numeric literal"));
                }
            }
            self.lex_exponent()?;
        }
        let raw: String = self.src[start..self.pos].iter().collect();
        self.check_no_ident_after_number()?;
        Ok(TokenKind::Num { raw, flags })
    }

    fn lex_decimal_digits(&mut self, _leading: bool) -> LexResult<()> {
        let mut any = false;
        let mut last_sep = false;
        while let Some(c) = self.peek() {
            if c == '_' {
                if !any || last_sep {
                    return Err(Fail::early("misplaced numeric separator"));
                }
                last_sep = true;
                self.pos += 1;
            } else if c.is_ascii_digit() {
                any = true;
                last_sep = false;
                self.pos += 1;
            } else {
                break;
            }
        }
        if !any || last_sep {
            return Err(Fail::early("malformed numeric literal"));
        }
        Ok(())
    }

    fn lex_exponent(&mut self) -> LexResult<()> {
        if matches!(self.peek(), Some('e') | Some('E')) {
            self.pos += 1;
            if matches!(self.peek(), Some('+') | Some('-')) {
                self.pos += 1;
            }
            if !self.peek().is_some_and(|c| c.is_ascii_digit()) {
                return Err(Fail::early("malformed exponent"));
            }
            self.lex_decimal_digits(false)?;
        }
        Ok(())
    }

    /// The SourceCharacter immediately following a NumericLiteral must not be
    /// an IdentifierStart or DecimalDigit.
    fn check_no_ident_after_number(&self) -> LexResult<()> {
        match self.peek() {
            Some(c) if is_id_start(c) || c.is_ascii_digit() || c == '\\' => {
                Err(Fail::early("identifier starts immediately after number"))
            }
            _ => Ok(()),
        }
    }

    fn lex_string(&mut self) -> LexResult<TokenKind> {
        let quote = self.bump().unwrap();
        let raw_start = self.pos;
        let mut flags = StrFlags::default();
        loop {
            match self.peek() {
                None => return Err(Fail::early("unterminated string literal")),
                Some(c) if c == '\n' || c == '\r' => {
                    return Err(Fail::early("line terminator in string literal"))
                }
                Some(c) if c == quote => {
                    let raw: String = self.src[raw_start..self.pos].iter().collect();
                    self.pos += 1;
                    return Ok(TokenKind::Str { raw, flags });
                }
                Some('\\') => {
                    flags.any_escape = true;
                    self.pos += 1;
                    self.lex_string_escape(&mut flags)?;
                }
                Some(_) => {
                    self.pos += 1;
                }
            }
        }
    }

    fn lex_string_escape(&mut self, flags: &mut StrFlags) -> LexResult<()> {
        match self.peek() {
            None => Err(Fail::early("unterminated string literal")),
            Some(c) if is_line_terminator(c) => {
                // LineContinuation; \r\n counts as one.
                self.pos += 1;
                if c == '\r' && self.peek() == Some('\n') {
                    self.pos += 1;
                }
                Ok(())
            }
            Some('x') => {
                self.pos += 1;
                for _ in 0..2 {
                    if self.peek().and_then(|c| c.to_digit(16)).is_none() {
                        return Err(Fail::early("malformed \\x escape"));
                    }
                    self.pos += 1;
                }
                Ok(())
            }
            Some('u') => {
                self.pos += 1;
                self.lex_unicode_escape_value()?;
                Ok(())
            }
            Some('0') if !self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) => {
                self.pos += 1;
                Ok(())
            }
            Some(c) if ('0'..='7').contains(&c) => {
                // LegacyOctalEscapeSequence.
                flags.legacy_octal_escape = true;
                self.pos += 1;
                if c <= '3' {
                    if self.peek().is_some_and(|d| ('0'..='7').contains(&d)) {
                        self.pos += 1;
                        if self.peek().is_some_and(|d| ('0'..='7').contains(&d)) {
                            self.pos += 1;
                        }
                    }
                } else if self.peek().is_some_and(|d| ('0'..='7').contains(&d)) {
                    self.pos += 1;
                }
                Ok(())
            }
            Some('8') | Some('9') => {
                flags.non_octal_escape = true;
                self.pos += 1;
                Ok(())
            }
            Some(_) => {
                self.pos += 1;
                Ok(())
            }
        }
    }

    /// Lex a template piece starting at `` ` `` (when `from_tick`) or at `}`
    /// (continuation). Produces NoSub/Head or Middle/Tail respectively.
    fn lex_template(&mut self, from_tick: bool) -> LexResult<TokenKind> {
        self.pos += 1; // consume ` or }
        let raw_start = self.pos;
        let mut invalid_escape = false;
        let mut octal_escape = false;
        loop {
            match self.peek() {
                None => return Err(Fail::early("unterminated template literal")),
                Some('`') => {
                    let raw: String = self.src[raw_start..self.pos].iter().collect();
                    self.pos += 1;
                    let kind = if from_tick { TplKind::NoSub } else { TplKind::Tail };
                    return Ok(TokenKind::Template {
                        kind,
                        raw,
                        invalid_escape,
                        octal_escape,
                    });
                }
                Some('$') if self.peek_at(1) == Some('{') => {
                    let raw: String = self.src[raw_start..self.pos].iter().collect();
                    self.pos += 2;
                    let kind = if from_tick { TplKind::Head } else { TplKind::Middle };
                    return Ok(TokenKind::Template {
                        kind,
                        raw,
                        invalid_escape,
                        octal_escape,
                    });
                }
                Some('\\') => {
                    self.pos += 1;
                    self.lex_template_escape(&mut invalid_escape, &mut octal_escape)?;
                }
                Some(_) => {
                    self.pos += 1;
                }
            }
        }
    }

    fn lex_template_escape(
        &mut self,
        invalid_escape: &mut bool,
        octal_escape: &mut bool,
    ) -> LexResult<()> {
        match self.peek() {
            None => Err(Fail::early("unterminated template literal")),
            Some(c) if is_line_terminator(c) => {
                self.pos += 1;
                if c == '\r' && self.peek() == Some('\n') {
                    self.pos += 1;
                }
                Ok(())
            }
            Some('x') => {
                self.pos += 1;
                for _ in 0..2 {
                    if self.peek().and_then(|c| c.to_digit(16)).is_none() {
                        *invalid_escape = true;
                        return Ok(());
                    }
                    self.pos += 1;
                }
                Ok(())
            }
            Some('u') => {
                self.pos += 1;
                let save = self.pos;
                if self.lex_unicode_escape_value().is_err() {
                    self.pos = save;
                    *invalid_escape = true;
                }
                Ok(())
            }
            Some('0') if !self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) => {
                self.pos += 1;
                Ok(())
            }
            Some(c) if c.is_ascii_digit() => {
                // Octal-ish escapes are not part of TemplateEscapeSequence:
                // invalid cooked value (error unless tagged).
                *octal_escape = true;
                self.pos += 1;
                Ok(())
            }
            Some(_) => {
                self.pos += 1;
                Ok(())
            }
        }
    }

    /// Re-lex a template continuation starting from a `}` token position.
    pub fn relex_template_continue(&mut self, rbrace_pos: usize) -> LexResult<Token> {
        self.pos = rbrace_pos;
        debug_assert_eq!(self.peek(), Some('}'));
        let start = self.pos;
        let kind = self.lex_template(false)?;
        Ok(Token {
            kind,
            start,
            end: self.pos,
            newline_before: false,
            had_escape: false,
        })
    }

    /// Re-lex a regex literal starting from a `/` (or `/=`) token position.
    pub fn relex_regex(&mut self, slash_pos: usize) -> LexResult<Token> {
        self.pos = slash_pos;
        debug_assert_eq!(self.peek(), Some('/'));
        let start = self.pos;
        self.pos += 1;
        let body_start = self.pos;
        let mut in_class = false;
        loop {
            match self.peek() {
                None => return Err(Fail::early("unterminated regular expression literal")),
                Some(c) if is_line_terminator(c) => {
                    return Err(Fail::early("line terminator in regular expression literal"))
                }
                Some('\\') => {
                    self.pos += 1;
                    match self.peek() {
                        None => {
                            return Err(Fail::early("unterminated regular expression literal"))
                        }
                        Some(c) if is_line_terminator(c) => {
                            return Err(Fail::early(
                                "line terminator in regular expression literal",
                            ))
                        }
                        Some(_) => {
                            self.pos += 1;
                        }
                    }
                }
                Some('[') => {
                    in_class = true;
                    self.pos += 1;
                }
                Some(']') if in_class => {
                    in_class = false;
                    self.pos += 1;
                }
                Some('/') if !in_class => break,
                Some(_) => {
                    self.pos += 1;
                }
            }
        }
        let pattern: String = self.src[body_start..self.pos].iter().collect();
        if pattern.is_empty() {
            // `//` can never reach here (it lexes as a comment), but `/=/`
            // has body "=". An empty body is impossible by construction.
            return Err(Fail::early("empty regular expression literal"));
        }
        self.pos += 1; // closing '/'
        let mut flags = String::new();
        while let Some(c) = self.peek() {
            if is_id_continue(c) {
                flags.push(c);
                self.pos += 1;
            } else if c == '\\' {
                return Err(Fail::early("escape in regular expression flags"));
            } else {
                break;
            }
        }
        Ok(Token {
            kind: TokenKind::Regex { pattern, flags },
            start,
            end: self.pos,
            newline_before: false,
            had_escape: false,
        })
    }

    fn lex_punct(&mut self) -> LexResult<TokenKind> {
        use P::*;
        macro_rules! t {
            ($n:expr, $p:expr) => {{
                self.pos += $n;
                return Ok(TokenKind::Punct($p));
            }};
        }
        let c0 = self.peek().unwrap();
        let c1 = self.peek_at(1);
        let c2 = self.peek_at(2);
        let c3 = self.peek_at(3);
        match c0 {
            '{' => t!(1, LBrace),
            '}' => t!(1, RBrace),
            '(' => t!(1, LParen),
            ')' => t!(1, RParen),
            '[' => t!(1, LBracket),
            ']' => t!(1, RBracket),
            ';' => t!(1, Semi),
            ',' => t!(1, Comma),
            ':' => t!(1, Colon),
            '~' => t!(1, Tilde),
            '.' => {
                if c1 == Some('.') && c2 == Some('.') {
                    t!(3, Ellipsis)
                }
                t!(1, Dot)
            }
            '<' => {
                if c1 == Some('<') {
                    if c2 == Some('=') {
                        t!(3, ShlEq)
                    }
                    t!(2, Shl)
                }
                if c1 == Some('=') {
                    t!(2, Le)
                }
                t!(1, Lt)
            }
            '>' => {
                if c1 == Some('>') {
                    if c2 == Some('>') {
                        if c3 == Some('=') {
                            t!(4, UShrEq)
                        }
                        t!(3, UShr)
                    }
                    if c2 == Some('=') {
                        t!(3, ShrEq)
                    }
                    t!(2, Shr)
                }
                if c1 == Some('=') {
                    t!(2, Ge)
                }
                t!(1, Gt)
            }
            '=' => {
                if c1 == Some('=') {
                    if c2 == Some('=') {
                        t!(3, EqEqEq)
                    }
                    t!(2, EqEq)
                }
                if c1 == Some('>') {
                    t!(2, Arrow)
                }
                t!(1, Eq)
            }
            '!' => {
                if c1 == Some('=') {
                    if c2 == Some('=') {
                        t!(3, NotEqEq)
                    }
                    t!(2, NotEq)
                }
                t!(1, Bang)
            }
            '+' => {
                if c1 == Some('+') {
                    t!(2, PlusPlus)
                }
                if c1 == Some('=') {
                    t!(2, PlusEq)
                }
                t!(1, Plus)
            }
            '-' => {
                if c1 == Some('-') {
                    t!(2, MinusMinus)
                }
                if c1 == Some('=') {
                    t!(2, MinusEq)
                }
                t!(1, Minus)
            }
            '*' => {
                if c1 == Some('*') {
                    if c2 == Some('=') {
                        t!(3, StarStarEq)
                    }
                    t!(2, StarStar)
                }
                if c1 == Some('=') {
                    t!(2, StarEq)
                }
                t!(1, Star)
            }
            '%' => {
                if c1 == Some('=') {
                    t!(2, PercentEq)
                }
                t!(1, Percent)
            }
            '&' => {
                if c1 == Some('&') {
                    if c2 == Some('=') {
                        t!(3, AmpAmpEq)
                    }
                    t!(2, AmpAmp)
                }
                if c1 == Some('=') {
                    t!(2, AmpEq)
                }
                t!(1, Amp)
            }
            '|' => {
                if c1 == Some('|') {
                    if c2 == Some('=') {
                        t!(3, PipePipeEq)
                    }
                    t!(2, PipePipe)
                }
                if c1 == Some('=') {
                    t!(2, PipeEq)
                }
                t!(1, Pipe)
            }
            '^' => {
                if c1 == Some('=') {
                    t!(2, CaretEq)
                }
                t!(1, Caret)
            }
            '?' => {
                if c1 == Some('?') {
                    if c2 == Some('=') {
                        t!(3, QuestionQuestionEq)
                    }
                    t!(2, QuestionQuestion)
                }
                if c1 == Some('.') {
                    // `?.` not followed by a decimal digit (else it is `?`
                    // then `.5` — conditional with fractional literal).
                    if !c2.is_some_and(|c| c.is_ascii_digit()) {
                        t!(2, QuestionDot)
                    }
                }
                t!(1, Question)
            }
            '/' => {
                if c1 == Some('=') {
                    t!(2, SlashEq)
                }
                t!(1, Slash)
            }
            other => Err(Fail::early(format!(
                "unexpected character U+{:04X}",
                other as u32
            ))),
        }
    }
}
