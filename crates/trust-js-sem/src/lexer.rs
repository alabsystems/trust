// Lexer for the bootstrap slice. Anything outside the slice (regex literals,
// legacy octal, unicode identifiers) is a refusal — a parse failure is
// NoCoverage upstream, never a guessed SyntaxError. Numeric separators and
// BigInt literals ARE in the slice. Untagged template literals are lexed as
// one composite token (cooked string parts + sub-token-streams for the
// substitutions).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::value::Units;
use num_bigint::BigInt;
use std::rc::Rc;

/// One piece of a template literal: a cooked string run, or the token stream
/// of one `${...}` substitution.
#[derive(Debug, Clone, PartialEq)]
pub enum TplPiece {
    Str(Units),
    Sub(Vec<Token>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Num(f64),
    /// A BigInt literal value (`123n`, `0x1fn`, ...), already parsed.
    BigInt(Rc<BigInt>),
    /// String literal payload + whether any escape sequence appeared (a
    /// directive prologue entry must be escape-free to count).
    Str(Units, bool),
    Ident(String),
    /// An IdentifierName containing \u escapes (post-substitution value).
    /// NEVER matches keywords syntactically; a true-ReservedWord StringValue
    /// is a SyntaxError in identifier positions (the parser judges).
    EscIdent(String),
    /// `#name` — a PrivateIdentifier (the bare name, no leading `#`). The
    /// parser judges where it is legal (member access / brand check only).
    PrivateIdent(String),
    Punct(&'static str),
    Template(Vec<TplPiece>),
    /// A regular-expression literal: `(body, flags)` as UTF-16 code units,
    /// WITHOUT the enclosing slashes. Pattern/flag VALIDITY is judged by the
    /// parser (via trust-js-regexp), never by the lexer.
    Regex(Units, Units),
    Eof,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub tok: Tok,
    /// A line terminator appeared between the previous token and this one
    /// (drives ASI and the restricted productions).
    pub newline_before: bool,
}

pub struct Lexer<'a> {
    chars: Vec<char>,
    pos: usize,
    _src: std::marker::PhantomData<&'a str>,
    /// Regex-vs-division goal (12.9). `true` where a `/` begins a
    /// RegularExpressionLiteral (an operand may begin here); `false` where it
    /// is a division / division-assign operator. Maintained by `update_context`.
    expr_allowed: bool,
    /// The bracket-context stack that disambiguates the genuinely
    /// context-dependent tokens (an object-literal `}` vs a block `}`, a
    /// function/class-EXPRESSION body `}` vs a DECLARATION body `}`, a
    /// control-head `)` vs a call/group `)`). The base entry keeps it non-empty.
    context: Vec<Ctx>,
    /// A classification of the previous significant token, carrying exactly the
    /// distinctions the context-update rules read.
    prev_type: PrevType,
}

/// One entry of the lexer's bracket-context stack.
#[derive(Clone, Copy, PartialEq)]
enum Ctx {
    /// `{` opening a block statement or a function/class body.
    BStat,
    /// `{` opening an object literal (an expression) — division follows `}`.
    BExpr,
    /// `(` of a control-flow head (`if`/`for`/`while`/`with`) — a regex may
    /// begin after the matching `)`.
    PStat,
    /// `(` of a call or a grouping (an expression) — division follows `)`.
    PExpr,
    /// A function/class EXPRESSION — its body is a value, so division follows
    /// the body `}`.
    FExpr,
    /// A function/class DECLARATION (a statement) — a regex may begin after
    /// the body `}`.
    FStat,
}

impl Ctx {
    /// The construct evaluates to a value (an operator/division follows).
    fn is_expr(self) -> bool {
        matches!(self, Ctx::BExpr | Ctx::PExpr | Ctx::FExpr)
    }
    /// A function/class context (its body brace pops through to it).
    fn is_func(self) -> bool {
        matches!(self, Ctx::FExpr | Ctx::FStat)
    }
}

/// A classification of the previous significant token, carrying exactly the
/// distinctions the context-update rules need (mirrors the per-token-type
/// dispatch a real engine's tokenizer performs).
#[derive(Clone, Copy, PartialEq)]
enum PrevType {
    /// Program (or `${…}`-substitution) start — treated as end-of-input.
    Start,
    /// A completed operand: a literal, `this`/`super`/`true`/`false`/`null`,
    /// `#name`, a `}`/`]`, or a postfix `++`/`--`.
    Value,
    /// An identifier (drives the contextual `of` rule).
    Name,
    /// `.`
    Dot,
    /// `{`
    BraceL,
    /// `)`
    ParenR,
    /// `:`
    Colon,
    /// `;`
    Semi,
    /// `=>`
    Arrow,
    /// `if` — a following `(` is a statement paren.
    KwIf,
    /// `for` — a following `(` is a statement paren.
    KwFor,
    /// `while` — a following `(` is a statement paren.
    KwWhile,
    /// `with` — a following `(` is a statement paren.
    KwWith,
    /// `return` — a following `{` is a block iff a line terminator precedes it.
    KwReturn,
    /// `else` — a following `{` is a block.
    KwElse,
    /// `function`/`class`.
    KwFunction,
    /// Any other punctuator or before-expression keyword (a `/` after it starts
    /// a regex).
    Op,
}

const PUNCTS: &[&str] = &[
    // longest-first within shared prefixes
    ">>>=", "===", "!==", ">>>", "**=", "<<=", ">>=", "...", "=>", "==", "!=", "<=", ">=", "&&",
    "||", "??", "?.", "++", "--", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "**",
    "{", "}", "(", ")", "[", "]", ";", ",", "<", ">", "+", "-", "*", "/", "%", "!", "?", ":", "=",
    ".", "&", "|", "^", "~",
];

/// `function`/`class` — a `/` after their body `}` depends on whether they
/// were an expression or a declaration.
fn is_function_kw(id: &str) -> bool {
    matches!(id, "function" | "class")
}

/// An IdentifierName that is NOT one of the keyword token types the context
/// machine treats specially (so it is a `Name`, driving the contextual `of`
/// rule). `var`/`let`/`const`/`await`/`async`/`of`/`get`/… all count as names.
fn is_name_ident(id: &str) -> bool {
    !matches!(
        id,
        "if" | "for"
            | "while"
            | "with"
            | "return"
            | "else"
            | "function"
            | "class"
            | "this"
            | "super"
            | "true"
            | "false"
            | "null"
            | "typeof"
            | "void"
            | "delete"
            | "new"
            | "in"
            | "instanceof"
            | "throw"
            | "case"
            | "do"
            | "yield"
    )
}

/// Classify a produced token for use as the NEXT token's `prev_type`.
fn classify(tok: &Tok) -> PrevType {
    match tok {
        Tok::Num(_)
        | Tok::BigInt(_)
        | Tok::Str(..)
        | Tok::Template(_)
        | Tok::Regex(..)
        | Tok::PrivateIdent(_) => PrevType::Value,
        Tok::EscIdent(_) => PrevType::Name,
        Tok::Ident(id) => match id.as_str() {
            "if" => PrevType::KwIf,
            "for" => PrevType::KwFor,
            "while" => PrevType::KwWhile,
            "with" => PrevType::KwWith,
            "return" => PrevType::KwReturn,
            "else" => PrevType::KwElse,
            "function" | "class" => PrevType::KwFunction,
            "this" | "super" | "true" | "false" | "null" => PrevType::Value,
            "typeof" | "void" | "delete" | "new" | "in" | "instanceof" | "throw" | "case"
            | "do" | "yield" => PrevType::Op,
            _ => PrevType::Name,
        },
        // `{`/`}`/`(`/`)` are handled by dedicated arms; their classification
        // here only matters when they appear as the PREVIOUS token.
        Tok::Punct(p) => match *p {
            "{" => PrevType::BraceL,
            ")" => PrevType::ParenR,
            "(" | "[" | "," => PrevType::Op, // before-expression openers/separators
            "}" | "]" | "++" | "--" | "?." => PrevType::Value,
            "." => PrevType::Dot,
            ":" => PrevType::Colon,
            ";" => PrevType::Semi,
            "=>" => PrevType::Arrow,
            _ => PrevType::Op, // every operator (`= + - * / % ! ~ ? < > == …`)
        },
        Tok::Eof => PrevType::Start,
    }
}

/// Whether a `/` begins a regex immediately after a token of this `prev_type`
/// (the token type's `[before expression]` flag).
fn prev_before_expr(p: PrevType) -> bool {
    matches!(
        p,
        PrevType::Op
            | PrevType::Colon
            | PrevType::Semi
            | PrevType::Arrow
            | PrevType::KwReturn
            | PrevType::KwElse
            | PrevType::BraceL
    )
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Lexer<'a> {
        Lexer {
            chars: src.chars().collect(),
            pos: 0,
            _src: std::marker::PhantomData,
            expr_allowed: true,
            context: vec![Ctx::BStat],
            prev_type: PrevType::Start,
        }
    }

    /// Update the regex-vs-division goal after producing `tok` (the acorn-style
    /// token-context algorithm). `newline_before` is whether a line terminator
    /// preceded `tok` (drives the `return`/`name`-brace block test).
    fn update_context(&mut self, tok: &Tok, newline_before: bool) {
        match tok {
            Tok::Punct("{") => {
                let block = self.brace_is_block(newline_before);
                self.context.push(if block { Ctx::BStat } else { Ctx::BExpr });
                self.expr_allowed = true;
            }
            Tok::Punct("}") | Tok::Punct(")") => {
                if self.context.len() <= 1 {
                    // Unbalanced close (or only the base remains): fall back to
                    // the operand goal, keeping the base context intact.
                    self.expr_allowed = true;
                } else if let Some(mut out) = self.context.pop() {
                    // A function/class body `}` pops the body block and then the
                    // enclosing function context, whose is_expr decides the goal.
                    if out == Ctx::BStat && self.context.last().is_some_and(|c| c.is_func()) {
                        if let Some(func) = self.context.pop() {
                            out = func;
                        }
                    }
                    self.expr_allowed = !out.is_expr();
                }
            }
            Tok::Punct("(") => {
                let stat = matches!(
                    self.prev_type,
                    PrevType::KwIf | PrevType::KwFor | PrevType::KwWhile | PrevType::KwWith
                );
                self.context.push(if stat { Ctx::PStat } else { Ctx::PExpr });
                self.expr_allowed = true;
            }
            Tok::Ident(id) if is_function_kw(id) => {
                let prev = self.prev_type;
                let top = self.context.last().copied();
                let is_expr = prev_before_expr(prev)
                    && prev != PrevType::KwElse
                    && !(prev == PrevType::Semi && top != Some(Ctx::PStat))
                    && !(prev == PrevType::KwReturn && newline_before)
                    && !((prev == PrevType::Colon || prev == PrevType::BraceL)
                        && top == Some(Ctx::BStat));
                self.context.push(if is_expr { Ctx::FExpr } else { Ctx::FStat });
                self.expr_allowed = false;
            }
            Tok::Ident(id) if is_name_ident(id) => {
                // The contextual `of`: a regex may follow only when `of` is the
                // for-of operator (it appeared in operator position); as an
                // operand identifier it is followed by division.
                self.expr_allowed = id == "of" && !self.expr_allowed;
            }
            Tok::EscIdent(id) => {
                self.expr_allowed = id == "of" && !self.expr_allowed;
            }
            _ => {
                self.expr_allowed = prev_before_expr(classify(tok));
            }
        }
        self.prev_type = classify(tok);
    }

    /// Whether a `{` at the current position opens a block/body (regex may
    /// begin after `}`) rather than an object literal (division after `}`).
    fn brace_is_block(&self, newline_before: bool) -> bool {
        // The base `Ctx::BStat` is never popped, so `last()` is always `Some`;
        // the fallback keeps the lexer total under any input regardless.
        let parent = self.context.last().copied().unwrap_or(Ctx::BStat);
        if parent.is_func() {
            return true; // a function/class body is a block
        }
        match self.prev_type {
            PrevType::Colon if matches!(parent, Ctx::BStat | Ctx::BExpr) => !parent.is_expr(),
            PrevType::KwReturn => newline_before,
            PrevType::Name if self.expr_allowed => newline_before,
            PrevType::KwElse
            | PrevType::Semi
            | PrevType::Start
            | PrevType::ParenR
            | PrevType::Arrow => true,
            PrevType::BraceL => parent == Ctx::BStat,
            PrevType::Name => false,
            _ => !self.expr_allowed,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn peek_at(&self, off: usize) -> Option<char> {
        self.chars.get(self.pos + off).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    /// Tokenize the whole source. Err = out-of-slice construct.
    pub fn tokenize(src: &str) -> Result<Vec<Token>, String> {
        let mut lx = Lexer::new(src);
        let mut out = Vec::new();
        loop {
            let (tok, nl) = lx.next_token()?;
            let is_eof = matches!(tok, Tok::Eof);
            lx.update_context(&tok, nl);
            out.push(Token {
                tok,
                newline_before: nl,
            });
            if is_eof {
                return Ok(out);
            }
        }
    }

    fn next_token(&mut self) -> Result<(Tok, bool), String> {
        let mut newline = false;
        loop {
            match self.peek() {
                None => return Ok((Tok::Eof, newline)),
                Some(c) if is_line_term(c) => {
                    newline = true;
                    self.pos += 1;
                }
                Some(c) if is_ws(c) => {
                    self.pos += 1;
                }
                Some('/') if self.peek_at(1) == Some('/') => {
                    while let Some(c) = self.peek() {
                        if is_line_term(c) {
                            break;
                        }
                        self.pos += 1;
                    }
                }
                Some('/') if self.peek_at(1) == Some('*') => {
                    self.pos += 2;
                    let mut closed = false;
                    while let Some(c) = self.bump() {
                        if is_line_term(c) {
                            newline = true; // multiline comment = line break for ASI
                        }
                        if c == '*' && self.peek() == Some('/') {
                            self.pos += 1;
                            closed = true;
                            break;
                        }
                    }
                    if !closed {
                        return Err("unterminated block comment".to_string());
                    }
                }
                Some('/') if self.expr_allowed => {
                    self.pos += 1; // consume the opening '/'
                    let (body, flags) = self.lex_regex()?;
                    return Ok((Tok::Regex(body, flags), newline));
                }
                Some('`') => {
                    self.pos += 1;
                    let t = self.lex_template()?;
                    return Ok((t, newline));
                }
                Some('#') => {
                    // A hashbang comment `#!...` is only legal at file start;
                    // it is out of slice — refuse rather than mis-lex.
                    if self.peek_at(1) == Some('!') && self.pos == 0 {
                        return Err("hashbang comment (out of slice)".to_string());
                    }
                    // `#name` — a PrivateIdentifier. The name after `#` follows
                    // IdentifierName lexing (ASCII, \u escapes); no separator.
                    self.pos += 1;
                    match self.peek() {
                        Some(c) if is_ident_start(c) || c == '\\' => {}
                        _ => return Err("`#` not followed by an identifier".to_string()),
                    }
                    let (name, _escaped) = self.lex_identifier_name()?;
                    return Ok((Tok::PrivateIdent(name), newline));
                }
                Some(_) => break,
            }
        }
        let c = self.peek().expect("non-eof");
        if c == '"' || c == '\'' {
            let (u, esc) = self.lex_string(c)?;
            return Ok((Tok::Str(u, esc), newline));
        }
        if c.is_ascii_digit() || (c == '.' && self.peek_at(1).is_some_and(|d| d.is_ascii_digit()))
        {
            return Ok((
                match self.lex_number()? {
                    NumLit::Num(n) => Tok::Num(n),
                    NumLit::Big(b) => Tok::BigInt(Rc::new(b)),
                },
                newline,
            ));
        }
        if is_ident_start(c) || c == '\\' {
            let (id, escaped) = self.lex_identifier_name()?;
            return Ok(
                (if escaped { Tok::EscIdent(id) } else { Tok::Ident(id) }, newline),
            );
        }
        for p in PUNCTS {
            if self.src_matches(p) {
                self.pos += p.chars().count();
                return Ok((Tok::Punct(p), newline));
            }
        }
        // A non-ASCII code point here is past whitespace, line-terminator and
        // IdentifierStart handling, so it cannot begin any token — a
        // conforming engine throws SyntaxError ("Invalid or unexpected
        // token"). ASCII stragglers stay an out-of-slice refusal (some may be
        // valid tokens we do not lex yet).
        if !c.is_ascii() {
            return Err(crate::parser::early_syntax(
                "unexpected non-ASCII character outside a string/comment",
            ));
        }
        Err(format!("unrecognized character {c:?}"))
    }

    /// IdentifierName with \uXXXX / \u{...} escapes substituted. The slice
    /// validates ASCII ID chars exactly; a non-ASCII substitution (or raw
    /// char) refuses — ID_Start/ID_Continue tables are out of slice.
    fn lex_identifier_name(&mut self) -> Result<(String, bool), String> {
        let mut out = String::new();
        let mut escaped = false;
        loop {
            match self.peek() {
                Some('\\') => {
                    self.pos += 1;
                    if self.bump() != Some('u') {
                        return Err("bad identifier escape (not \\u)".to_string());
                    }
                    let cp: u32 = if self.peek() == Some('{') {
                        self.pos += 1;
                        let mut v: u32 = 0;
                        let mut any = false;
                        while let Some(d) = self.peek() {
                            if d == '}' {
                                break;
                            }
                            let dv = d
                                .to_digit(16)
                                .ok_or_else(|| "bad \\u{} identifier escape".to_string())?;
                            v = v * 16 + dv;
                            if v > 0x10_ffff {
                                return Err("identifier escape out of range".to_string());
                            }
                            any = true;
                            self.pos += 1;
                        }
                        if !any || self.bump() != Some('}') {
                            return Err("bad \\u{} identifier escape".to_string());
                        }
                        v
                    } else {
                        self.hex_digits(4)?
                    };
                    // A surrogate code point (0xD800..=0xDFFF) has no
                    // IdentifierStart/Part property; a real engine throws a
                    // SyntaxError for `\uD800`-style identifier escapes.
                    let Some(c) = char::from_u32(cp) else {
                        return Err(crate::parser::early_syntax(
                            "identifier escape is a surrogate code point",
                        ));
                    };
                    let valid = if out.is_empty() {
                        is_ident_start(c)
                    } else {
                        is_ident_part(c)
                    };
                    if !valid {
                        // The escaped code point is not an identifier character
                        // (exact ID_Start/ID_Continue tables): a pinned
                        // SyntaxError, matching a conforming engine.
                        return Err(crate::parser::early_syntax(
                            "identifier escape is not an identifier character",
                        ));
                    }
                    out.push(c);
                    escaped = true;
                }
                Some(c) if !out.is_empty() && is_ident_part(c) => {
                    out.push(c);
                    self.pos += 1;
                }
                Some(c) if out.is_empty() && is_ident_start(c) => {
                    out.push(c);
                    self.pos += 1;
                }
                _ => break,
            }
        }
        if out.is_empty() {
            return Err("empty identifier".to_string());
        }
        Ok((out, escaped))
    }

    /// Lex a RegularExpressionLiteral body + flags after the opening `/`
    /// (12.9.5). Purely SYNTACTIC: `[` opens a class within which `/` is a
    /// literal char and only `]` closes; `\` escapes the next
    /// (non-line-terminator) char. A LineTerminator or EOF before the closing
    /// `/` is a SyntaxError. Pattern/flag validity is left to the parser.
    fn lex_regex(&mut self) -> Result<(Units, Units), String> {
        let mut body: Units = Vec::new();
        let mut in_class = false;
        loop {
            let c = self.bump().ok_or_else(|| {
                crate::parser::early_syntax("unterminated regular expression literal")
            })?;
            if is_line_term(c) {
                return Err(crate::parser::early_syntax(
                    "line terminator in regular expression literal",
                ));
            }
            match c {
                '\\' => {
                    push_char(&mut body, c);
                    let n = self.bump().ok_or_else(|| {
                        crate::parser::early_syntax("unterminated regular expression literal")
                    })?;
                    if is_line_term(n) {
                        return Err(crate::parser::early_syntax(
                            "line terminator in regular expression literal",
                        ));
                    }
                    push_char(&mut body, n);
                }
                '[' => {
                    in_class = true;
                    push_char(&mut body, c);
                }
                ']' => {
                    in_class = false;
                    push_char(&mut body, c);
                }
                '/' if !in_class => break,
                _ => push_char(&mut body, c),
            }
        }
        // Flags: a run of IdentifierPart characters (validity judged later).
        // \u escapes in flags are NOT part of RegularExpressionFlags's
        // IdentifierPartChar, so a following `\` ends the run.
        let mut flags: Units = Vec::new();
        while let Some(c) = self.peek() {
            if is_ident_part(c) {
                push_char(&mut flags, c);
                self.pos += 1;
            } else {
                break;
            }
        }
        Ok((body, flags))
    }

    fn src_matches(&self, p: &str) -> bool {
        p.chars()
            .enumerate()
            .all(|(i, pc)| self.peek_at(i) == Some(pc))
    }

    /// Lex a template literal after the opening backtick: cooked string runs
    /// and `${...}` substitution token streams, as one composite token.
    fn lex_template(&mut self) -> Result<Tok, String> {
        let mut pieces: Vec<TplPiece> = Vec::new();
        let mut cur: Units = Vec::new();
        loop {
            let c = self
                .bump()
                .ok_or_else(|| "unterminated template literal".to_string())?;
            match c {
                '`' => {
                    pieces.push(TplPiece::Str(cur));
                    return Ok(Tok::Template(pieces));
                }
                '$' if self.peek() == Some('{') => {
                    self.pos += 1;
                    pieces.push(TplPiece::Str(std::mem::take(&mut cur)));
                    pieces.push(TplPiece::Sub(self.lex_template_sub()?));
                }
                '\\' => {
                    self.lex_escape(&mut cur, true)?;
                }
                '\r' => {
                    // Cooked: <CR> and <CRLF> normalize to <LF>.
                    if self.peek() == Some('\n') {
                        self.pos += 1;
                    }
                    cur.push(0x0a);
                }
                c => push_char(&mut cur, c),
            }
        }
    }

    /// Collect the token stream of one `${...}` substitution (brace-balanced,
    /// exclusive of the closing `}`). A substitution is an independent
    /// expression, so it runs the goal machine on a fresh context (`expr_allowed`
    /// true, prev-type before-expression so a leading `{` is an object literal);
    /// the outer goal state is saved and restored around it.
    fn lex_template_sub(&mut self) -> Result<Vec<Token>, String> {
        let saved_expr = self.expr_allowed;
        let saved_prev = self.prev_type;
        let saved_ctx = std::mem::replace(&mut self.context, vec![Ctx::BStat]);
        self.expr_allowed = true;
        self.prev_type = PrevType::Op;
        let out = self.lex_template_sub_inner();
        self.expr_allowed = saved_expr;
        self.prev_type = saved_prev;
        self.context = saved_ctx;
        out
    }

    fn lex_template_sub_inner(&mut self) -> Result<Vec<Token>, String> {
        let mut toks: Vec<Token> = Vec::new();
        let mut depth: u32 = 1;
        loop {
            let (tok, nl) = self.next_token()?;
            match &tok {
                Tok::Eof => return Err("unterminated template substitution".to_string()),
                Tok::Punct("{") => depth += 1,
                Tok::Punct("}") => {
                    depth -= 1;
                    if depth == 0 {
                        toks.push(Token {
                            tok: Tok::Eof,
                            newline_before: nl,
                        });
                        return Ok(toks);
                    }
                }
                _ => {}
            }
            self.update_context(&tok, nl);
            toks.push(Token {
                tok,
                newline_before: nl,
            });
        }
    }

    /// One escape sequence after the backslash. `in_template` refuses the
    /// template-specific ill-formed escapes rather than guessing.
    fn lex_escape(&mut self, out: &mut Units, in_template: bool) -> Result<(), String> {
        let e = self
            .bump()
            .ok_or_else(|| "unterminated escape".to_string())?;
        match e {
            'n' => out.push(0x0a),
            't' => out.push(0x09),
            'r' => out.push(0x0d),
            'b' => out.push(0x08),
            'f' => out.push(0x0c),
            'v' => out.push(0x0b),
            '0' => {
                if self.peek().is_some_and(|d| d.is_ascii_digit()) {
                    return Err("legacy octal escape (out of slice)".to_string());
                }
                out.push(0);
            }
            '1'..='9' => return Err("legacy octal escape (out of slice)".to_string()),
            'x' => {
                // Ill-formed \xHH in a STRING is a pinned early SyntaxError;
                // in a template it may cook to undefined under a tag (the
                // tagged form is refused at parse), so only strings claim it.
                let h = self.hex_digits(2).map_err(|e| {
                    if in_template {
                        e
                    } else {
                        crate::parser::early_syntax("ill-formed \\x escape in string literal")
                    }
                })?;
                out.push(u16::try_from(h).expect("two hex digits"));
            }
            'u' => {
                if self.peek() == Some('{') {
                    self.pos += 1;
                    let mut v: u32 = 0;
                    let mut any = false;
                    while let Some(d) = self.peek() {
                        if d == '}' {
                            break;
                        }
                        let dv = d
                            .to_digit(16)
                            .ok_or_else(|| "bad \\u{} escape".to_string())?;
                        v = v * 16 + dv;
                        if v > 0x10_ffff {
                            return Err("\\u{} escape out of range".to_string());
                        }
                        any = true;
                        self.pos += 1;
                    }
                    if !any || self.bump() != Some('}') {
                        return Err("bad \\u{} escape".to_string());
                    }
                    push_code_point(out, v);
                } else {
                    let h = self.hex_digits(4)?;
                    out.push(u16::try_from(h).expect("four hex digits"));
                }
            }
            c if is_line_term(c) => {
                // Line continuation: contributes nothing. \r\n is one.
                if c == '\r' && self.peek() == Some('\n') {
                    self.pos += 1;
                }
            }
            other => {
                let _ = in_template;
                push_char(out, other); // identity escape
            }
        }
        Ok(())
    }

    fn lex_string(&mut self, quote: char) -> Result<(Units, bool), String> {
        self.pos += 1;
        let mut out: Units = Vec::new();
        let mut had_escape = false;
        loop {
            let c = self
                .bump()
                .ok_or_else(|| "unterminated string".to_string())?;
            if c == quote {
                return Ok((out, had_escape));
            }
            if is_line_term(c) {
                return Err("line terminator in string".to_string());
            }
            if c != '\\' {
                push_char(&mut out, c);
                continue;
            }
            had_escape = true;
            self.lex_escape(&mut out, false)?;
        }
    }

    fn hex_digits(&mut self, n: usize) -> Result<u32, String> {
        let mut v = 0u32;
        for _ in 0..n {
            let d = self
                .bump()
                .and_then(|c| c.to_digit(16))
                .ok_or_else(|| "bad hex escape".to_string())?;
            v = v * 16 + d;
        }
        Ok(v)
    }

    /// Read a maximal run of `radix` digits with legal NumericLiteralSeparator
    /// (`_`) placement (never leading, trailing, doubled, or non-adjacent to a
    /// digit). Returns the digits with separators removed (possibly empty).
    fn read_digits_sep(&mut self, radix: u32) -> Result<String, String> {
        let mut out = String::new();
        loop {
            match self.peek() {
                Some(c) if c.is_digit(radix) => {
                    out.push(c);
                    self.pos += 1;
                }
                Some('_') => {
                    // A NumericLiteralSeparator must sit strictly between two
                    // digits of the run (never leading, trailing, or doubled).
                    // A misplaced separator is a fully-specified early
                    // SyntaxError in every mode (12.9.3).
                    if out.is_empty() || !self.peek_at(1).is_some_and(|d| d.is_digit(radix)) {
                        return Err(crate::parser::early_syntax(
                            "misplaced numeric separator `_`",
                        ));
                    }
                    self.pos += 1;
                }
                _ => break,
            }
        }
        Ok(out)
    }

    fn lex_number(&mut self) -> Result<NumLit, String> {
        if self.peek() == Some('0')
            && self
                .peek_at(1)
                .is_some_and(|c| matches!(c, 'x' | 'X' | 'o' | 'O' | 'b' | 'B'))
        {
            let radix_char = self.peek_at(1).expect("checked");
            let radix = match radix_char {
                'x' | 'X' => 16,
                'o' | 'O' => 8,
                _ => 2,
            };
            self.pos += 2;
            let digits = self.read_digits_sep(radix)?;
            if digits.is_empty() {
                return Err("empty radix literal".to_string());
            }
            // BigInt suffix: `0x1fn`.
            if self.peek() == Some('n') {
                self.pos += 1;
                self.check_ident_after()?;
                return Ok(NumLit::Big(self.parse_big(&digits, radix)?));
            }
            self.check_number_tail()?;
            let v = u128::from_str_radix(&digits, radix)
                .map_err(|_| "radix literal overflows u128 (out of slice)".to_string())?;
            #[allow(clippy::cast_precision_loss)] // u128->f64 rounds to nearest (spec rounding)
            return Ok(NumLit::Num(v as f64));
        }
        // A leading `0` in a decimal literal.
        if self.peek() == Some('0') {
            match self.peek_at(1) {
                // Legacy octal / non-octal-decimal (`00`, `08`): sloppy-legal,
                // strict SyntaxError, and unmodeled — a sound refusal.
                Some(c) if c.is_ascii_digit() => {
                    return Err("legacy octal / leading-zero literal (out of slice)".to_string());
                }
                // `0_…`: a NumericLiteralSeparator adjacent to a leading `0`
                // (a LegacyOctalLikeDecimal / NonOctalDecimal integer literal)
                // is a SyntaxError in every mode (12.9.3).
                Some('_') => {
                    return Err(crate::parser::early_syntax(
                        "numeric separator adjacent to a leading `0`",
                    ));
                }
                _ => {}
            }
        }
        let int_digits = self.read_digits_sep(10)?;
        let mut text = int_digits.clone();
        let mut integer_only = true;
        if self.peek() == Some('.') {
            integer_only = false;
            text.push('.');
            self.pos += 1;
            let frac = self.read_digits_sep(10)?;
            text.push_str(&frac);
        }
        // A literal must have at least one digit (guards a bare ".").
        if text.chars().all(|c| !c.is_ascii_digit()) {
            return Err("number literal with no digits".to_string());
        }
        if self.peek().is_some_and(|c| c == 'e' || c == 'E') {
            integer_only = false;
            text.push('e');
            self.pos += 1;
            if self.peek().is_some_and(|c| c == '+' || c == '-') {
                text.push(self.peek().expect("checked"));
                self.pos += 1;
            }
            let exp = self.read_digits_sep(10)?;
            if exp.is_empty() {
                return Err("missing exponent digits".to_string());
            }
            text.push_str(&exp);
        }
        // BigInt suffix: only on an integer decimal (`0n`, `123n`) — never on a
        // fractional or exponential literal (that is an early SyntaxError,
        // reproduced as a parse failure → NoCoverage).
        if self.peek() == Some('n') {
            if !integer_only {
                // A BigInt suffix on a fractional/exponential literal (`1.5n`,
                // `1e3n`) is a fully-specified early SyntaxError.
                return Err(crate::parser::early_syntax(
                    "BigInt suffix on a non-integer literal",
                ));
            }
            self.pos += 1;
            self.check_ident_after()?;
            return Ok(NumLit::Big(self.parse_big(&int_digits, 10)?));
        }
        self.check_number_tail()?;
        text.parse::<f64>()
            .map(NumLit::Num)
            .map_err(|e| format!("number literal parse: {e}"))
    }

    /// Parse cleaned `digits` in `radix` into a BigInt, refusing an
    /// astronomically large literal (out of slice).
    fn parse_big(&self, digits: &str, radix: u32) -> Result<BigInt, String> {
        let per_digit = u64::from(64 - (u64::from(radix) - 1).leading_zeros());
        if (digits.len() as u64).saturating_mul(per_digit) > crate::bigint::MAX_BITS {
            return Err("BigInt literal beyond the model cap (out of slice)".to_string());
        }
        BigInt::parse_bytes(digits.as_bytes(), radix)
            .ok_or_else(|| "BigInt literal parse".to_string())
    }

    /// After a number (or its `n` suffix): no identifier char or digit may
    /// immediately follow (`3in`, `1n2` are errors).
    fn check_ident_after(&self) -> Result<(), String> {
        match self.peek() {
            // An IdentifierStart or DecimalDigit immediately after a BigInt
            // literal (`1n2`, `0x1fn9`) is a fully-specified early SyntaxError.
            Some(c) if is_ident_start(c) || c.is_ascii_digit() => Err(crate::parser::early_syntax(
                "identifier immediately after numeric literal",
            )),
            _ => Ok(()),
        }
    }

    fn check_number_tail(&self) -> Result<(), String> {
        match self.peek() {
            Some('_') => Err("trailing numeric separator".to_string()),
            Some(c) if is_ident_start(c) || c.is_ascii_digit() => {
                Err("identifier immediately after number".to_string())
            }
            _ => Ok(()),
        }
    }
}

/// The value of a numeric literal: an f64 or a BigInt.
enum NumLit {
    Num(f64),
    Big(BigInt),
}

fn push_char(out: &mut Units, c: char) {
    let mut buf = [0u16; 2];
    out.extend_from_slice(c.encode_utf16(&mut buf));
}

fn push_code_point(out: &mut Units, v: u32) {
    if let Some(c) = char::from_u32(v) {
        push_char(out, c);
    } else {
        // Lone surrogate from \u{d800}-style escape: keep the raw unit.
        out.push(u16::try_from(v & 0xffff).expect("masked"));
    }
}

fn is_ws(c: char) -> bool {
    matches!(
        c,
        '\t' | '\u{b}'
            | '\u{c}'
            | ' '
            | '\u{a0}'
            | '\u{feff}'
            | '\u{1680}'
            | '\u{2000}'..='\u{200a}'
            | '\u{202f}'
            | '\u{205f}'
            | '\u{3000}'
    )
}

fn is_line_term(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

fn is_ident_start(c: char) -> bool {
    if c.is_ascii() {
        // JS IdentifierStartChar = UnicodeIDStart | `$` | `_`.
        return c.is_ascii_alphabetic() || c == '_' || c == '$';
    }
    crate::unicode_id::is_unicode_id_start(c as u32)
}

fn is_ident_part(c: char) -> bool {
    if c.is_ascii() {
        // JS IdentifierPartChar = UnicodeIDContinue | `$` | <ZWNJ> | <ZWJ>;
        // ASCII `_`/digits are covered by ID_Continue, `$` is the extra.
        return c.is_ascii_alphanumeric() || c == '_' || c == '$';
    }
    // <ZWNJ> (U+200C) and <ZWJ> (U+200D) are added by JS on top of the
    // Unicode ID_Continue property.
    c == '\u{200c}' || c == '\u{200d}' || crate::unicode_id::is_unicode_id_continue(c as u32)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::units_from_str;

    fn toks(src: &str) -> Vec<Tok> {
        Lexer::tokenize(src)
            .expect("lexes")
            .into_iter()
            .map(|t| t.tok)
            .collect()
    }

    #[test]
    fn basic_stream() {
        assert_eq!(
            toks("var x = 1.5; // c"),
            vec![
                Tok::Ident("var".into()),
                Tok::Ident("x".into()),
                Tok::Punct("="),
                Tok::Num(1.5),
                Tok::Punct(";"),
                Tok::Eof
            ]
        );
    }

    #[test]
    fn string_escapes() {
        assert_eq!(
            toks(r#""a\nbA\x42""#),
            vec![Tok::Str(units_from_str("a\nbAB"), true), Tok::Eof]
        );
        assert_eq!(
            toks("'plain'"),
            vec![Tok::Str(units_from_str("plain"), false), Tok::Eof]
        );
    }

    #[test]
    fn division_vs_regex() {
        assert_eq!(
            toks("a / b"),
            vec![
                Tok::Ident("a".into()),
                Tok::Punct("/"),
                Tok::Ident("b".into()),
                Tok::Eof
            ]
        );
        // A regex literal now lexes to a Regex token in regex-goal position.
        assert_eq!(
            toks("var r = /ab/g;"),
            vec![
                Tok::Ident("var".into()),
                Tok::Ident("r".into()),
                Tok::Punct("="),
                Tok::Regex(units_from_str("ab"), units_from_str("g")),
                Tok::Punct(";"),
                Tok::Eof
            ]
        );
        // A class hides the delimiter; `\/` is escaped; flags follow.
        assert_eq!(
            toks("/[a/b]\\/c/gi"),
            vec![
                Tok::Regex(units_from_str("[a/b]\\/c"), units_from_str("gi")),
                Tok::Eof
            ]
        );
        // After a value, `/` is division, not a regex.
        assert_eq!(
            toks("a / b / c"),
            vec![
                Tok::Ident("a".into()),
                Tok::Punct("/"),
                Tok::Ident("b".into()),
                Tok::Punct("/"),
                Tok::Ident("c".into()),
                Tok::Eof
            ]
        );
        // Unterminated / line-terminator regex literals refuse.
        assert!(Lexer::tokenize("var r = /ab").is_err());
        assert!(Lexer::tokenize("var r = /a\nb/").is_err());
        assert!(Lexer::tokenize("07").is_err());
        // Legacy octal / leading-zero remains out of slice.
        assert!(Lexer::tokenize("08").is_err());
        // BigInt literals now lex to a BigInt token; separators are legal.
        assert!(matches!(
            Lexer::tokenize("0o777n").unwrap()[0].tok,
            Tok::BigInt(_)
        ));
        assert!(matches!(Lexer::tokenize("123n").unwrap()[0].tok, Tok::BigInt(_)));
        assert!(matches!(Lexer::tokenize("0x1fn").unwrap()[0].tok, Tok::BigInt(_)));
        assert!(matches!(Lexer::tokenize("1_000").unwrap()[0].tok, Tok::Num(_)));
        assert!(matches!(Lexer::tokenize("1_000n").unwrap()[0].tok, Tok::BigInt(_)));
        // Misplaced separators and bad BigInt suffixes are lexer errors.
        assert!(Lexer::tokenize("1__0").is_err());
        assert!(Lexer::tokenize("1_").is_err());
        assert!(Lexer::tokenize("1.5n").is_err());
        assert!(Lexer::tokenize("1e3n").is_err());
        assert!(Lexer::tokenize("1n2").is_err());
    }

    /// Context-driven regex-vs-division: a `/` is a RegularExpressionLiteral
    /// only in operand position; after a complete primary/member/call
    /// expression (including an object-literal or function-expression `}`) it is
    /// division. Mirrors a real engine's tokenizer goal-symbol tracking.
    #[test]
    fn regex_division_context() {
        // `true` iff any `Tok::Regex` appears in the (successful) token stream,
        // recursing into template-substitution sub-streams.
        fn any_regex(ts: &[Tok]) -> bool {
            ts.iter().any(|t| match t {
                Tok::Regex(..) => true,
                Tok::Template(pieces) => pieces.iter().any(|p| match p {
                    TplPiece::Sub(sub) => any_regex(&sub.iter().map(|t| t.tok.clone()).collect::<Vec<_>>()),
                    TplPiece::Str(_) => false,
                }),
                _ => false,
            })
        }
        fn has_regex(src: &str) -> bool {
            any_regex(&toks(src))
        }

        // --- division after a value-producing close --------------------------
        // Object literal `}` in expression position → division.
        assert!(!has_regex("({a:1} / 1)"));
        assert!(!has_regex("if ({valueOf:function(){return 1}} / 1 !== 1) {}"));
        // Function-EXPRESSION body `}` → division (the whole fn is a value).
        assert!(!has_regex("(function(){return 1} / {})"));
        assert!(!has_regex("isNaN(function(){return 1} / {})"));
        // Array `]`, call `)`, postfix `++` → division.
        assert!(!has_regex("[] / 1"));
        assert!(!has_regex("f() / 1"));
        assert!(!has_regex("x++ / 1"));
        assert!(!has_regex("a / b / c"));
        // Contextual `of` as an operand identifier → division (no ASI magic).
        assert!(!has_regex("instance/of/g"));

        // --- regex in operand position --------------------------------------
        // A block `}` (statement position) → the next `/` starts a regex.
        assert!(has_regex("if (x) {} /re/.test(y)"));
        assert!(has_regex("{}\n/re/g"));
        // Function-DECLARATION body `}` → regex.
        assert!(has_regex("function f(){}\n/re/.test(y)"));
        // Control-head `)` → regex (the statement body is an operand).
        assert!(has_regex("if (x) /re/.test(y)"));
        assert!(has_regex("while (x) /re/.test(y)"));
        // After before-expression keywords → regex.
        assert!(has_regex("return /re/g"));
        assert!(has_regex("typeof /re/"));
        assert!(has_regex("void /re/"));
        assert!(has_regex("x = a ? /re/ : /re2/"));
        // The for-of operator `of` DOES permit a following regex operand.
        assert!(has_regex("for (x of /re/) {}"));
        // Leading regex (program start is operand position).
        assert!(has_regex("/re/.test(y)"));

        // --- template substitutions run an independent goal ------------------
        // `${ {a:1} / 2 }`: the inner object-literal `}` → division, no regex.
        assert!(!has_regex("`${ {a:1} / 2 }`"));
        // `${ /re/ }`: operand position inside the substitution → regex.
        assert!(has_regex("`${ /re/g }`"));
    }

    #[test]
    fn template_literals() {
        // Simple cooked run.
        let ts = toks("`ab${x}c`");
        let Tok::Template(pieces) = &ts[0] else {
            panic!("expected template, got {ts:?}");
        };
        assert_eq!(pieces.len(), 3);
        assert_eq!(pieces[0], TplPiece::Str(units_from_str("ab")));
        let TplPiece::Sub(sub) = &pieces[1] else {
            panic!("expected sub");
        };
        assert_eq!(sub[0].tok, Tok::Ident("x".into()));
        assert_eq!(sub[1].tok, Tok::Eof);
        assert_eq!(pieces[2], TplPiece::Str(units_from_str("c")));
        // Nested braces inside a substitution; newline normalization.
        let ts = toks("`a${ {b: 1}.b }z\r\nq`");
        let Tok::Template(pieces) = &ts[0] else {
            panic!("expected template");
        };
        assert_eq!(pieces.last(), Some(&TplPiece::Str(units_from_str("z\nq"))));
        // Unterminated refuses.
        assert!(Lexer::tokenize("`abc").is_err());
        assert!(Lexer::tokenize("`a${1`").is_err());
    }

    #[test]
    fn newline_tracking() {
        let ts = Lexer::tokenize("a\nb").expect("lexes");
        assert!(!ts[0].newline_before);
        assert!(ts[1].newline_before);
    }
}
