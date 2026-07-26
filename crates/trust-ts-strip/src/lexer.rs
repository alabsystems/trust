// trust-ts-strip: a self-contained TS/JS tokenizer.
//
// Produces a flat token stream over byte offsets. Trivia (whitespace, line
// terminators, comments) is not emitted, but `nl_before` records whether a
// line terminator preceded a token (for ASI-lite in the eraser). Regex-vs-
// divide is resolved by the classic previous-significant-token heuristic;
// template substitutions are lexed inline via a brace/template stack, so the
// eraser sees ordinary tokens between the `Template*` delimiter tokens.
//
// The tokenizer is TS-agnostic: TS type syntax is just identifiers and
// punctuators at the lexical level, so nothing here knows about types.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// Punctuator kinds. Multi-char punctuators are matched maximally.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pk {
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Semi,
    Comma,
    Dot,
    Ellipsis,
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
    Slash,
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
    QQ,
    Question,
    QDot,
    Colon,
    Arrow,
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
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
    QQEq,
    At,
}

/// Token kinds. The concrete text of an `Ident`/`Private` etc. is recovered
/// from `src[start..end]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tk {
    Ident,
    Private,
    Num,
    Str,
    Regex,
    /// `` `...` `` with no substitution.
    TemplateFull,
    /// `` `...${ ``
    TemplateHead,
    /// `` }...${ ``
    TemplateMiddle,
    /// `` }...` ``
    TemplateTail,
    Punct(Pk),
    Eof,
}

#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub kind: Tk,
    pub start: usize,
    pub end: usize,
    /// A line terminator appeared in the trivia preceding this token.
    pub nl_before: bool,
}

fn is_id_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_' || b == b'$' || b >= 0x80
}
fn is_id_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'$' || b >= 0x80
}

/// What the previous significant token implies for a following `/`.
#[derive(Clone, Copy)]
enum RegexState {
    /// `/` begins a regular expression (operand position).
    Allowed,
    /// `/` is the division operator (after-operand position).
    Div,
}

/// Keywords after which an expression (hence a regex) is expected.
fn keyword_allows_regex(word: &str) -> bool {
    matches!(
        word,
        "return"
            | "typeof"
            | "instanceof"
            | "in"
            | "of"
            | "case"
            | "delete"
            | "void"
            | "do"
            | "else"
            | "yield"
            | "await"
            | "new"
            | "throw"
    )
}

/// Tokenize `src`. Returns a token vector terminated by an `Eof` token, or a
/// lexical-error message (which the eraser turns into a sound refusal).
pub fn lex(src: &str) -> Result<Vec<Token>, String> {
    let b = src.as_bytes();
    let n = b.len();
    let mut i = 0usize;
    let mut out: Vec<Token> = Vec::new();
    let mut regex_state = RegexState::Allowed;
    // Stack elements: true = template substitution (a `}` resumes a template),
    // false = ordinary brace.
    let mut brace_stack: Vec<bool> = Vec::new();
    let mut nl_pending = false;

    macro_rules! push {
        ($kind:expr, $start:expr, $end:expr) => {{
            out.push(Token { kind: $kind, start: $start, end: $end, nl_before: nl_pending });
            nl_pending = false;
        }};
    }

    while i < n {
        let c = b[i];
        // Trivia: whitespace and line terminators.
        if c == b'\n' || c == b'\r' {
            nl_pending = true;
            i += 1;
            continue;
        }
        if c == b' ' || c == b'\t' || c == 0x0c || c == 0x0b {
            i += 1;
            continue;
        }
        // Non-ASCII whitespace (NBSP etc.) — treat leading bytes of common
        // whitespace conservatively: only ASCII handled; other >=0x80 bytes
        // fall through to identifier handling.
        // Comments.
        if c == b'/' && i + 1 < n && b[i + 1] == b'/' {
            i += 2;
            while i < n && b[i] != b'\n' && b[i] != b'\r' {
                i += 1;
            }
            continue;
        }
        if c == b'/' && i + 1 < n && b[i + 1] == b'*' {
            i += 2;
            let mut closed = false;
            while i + 1 < n {
                if b[i] == b'\n' || b[i] == b'\r' {
                    nl_pending = true;
                }
                if b[i] == b'*' && b[i + 1] == b'/' {
                    i += 2;
                    closed = true;
                    break;
                }
                i += 1;
            }
            if !closed {
                return Err("unterminated block comment".to_string());
            }
            continue;
        }

        let start = i;

        // Identifiers / keywords.
        if is_id_start(c) {
            i += 1;
            while i < n && is_id_continue(b[i]) {
                i += 1;
            }
            let word = &src[start..i];
            push!(Tk::Ident, start, i);
            regex_state =
                if keyword_allows_regex(word) { RegexState::Allowed } else { RegexState::Div };
            continue;
        }

        // Private name `#ident`.
        if c == b'#' && i + 1 < n && is_id_start(b[i + 1]) {
            i += 1;
            while i < n && is_id_continue(b[i]) {
                i += 1;
            }
            push!(Tk::Private, start, i);
            regex_state = RegexState::Div;
            continue;
        }

        // Numbers.
        if c.is_ascii_digit() || (c == b'.' && i + 1 < n && b[i + 1].is_ascii_digit()) {
            i = scan_number(b, i);
            push!(Tk::Num, start, i);
            regex_state = RegexState::Div;
            continue;
        }

        // Strings.
        if c == b'"' || c == b'\'' {
            i += 1;
            let mut closed = false;
            while i < n {
                let d = b[i];
                if d == b'\\' {
                    i += 2;
                    continue;
                }
                if d == b'\n' || d == b'\r' {
                    break;
                }
                if d == c {
                    i += 1;
                    closed = true;
                    break;
                }
                i += 1;
            }
            if !closed {
                return Err("unterminated string literal".to_string());
            }
            push!(Tk::Str, start, i);
            regex_state = RegexState::Div;
            continue;
        }

        // Template literals.
        if c == b'`' {
            let (end, has_sub) = scan_template_piece(b, i + 1)
                .ok_or_else(|| "unterminated template literal".to_string())?;
            if has_sub {
                push!(Tk::TemplateHead, start, end);
                brace_stack.push(true);
                regex_state = RegexState::Allowed;
            } else {
                push!(Tk::TemplateFull, start, end);
                regex_state = RegexState::Div;
            }
            i = end;
            continue;
        }

        // Regex vs divide.
        if c == b'/' {
            if matches!(regex_state, RegexState::Allowed) {
                if let Some(end) = scan_regex(b, i) {
                    push!(Tk::Regex, start, end);
                    i = end;
                    regex_state = RegexState::Div;
                    continue;
                }
                return Err("unterminated regular expression".to_string());
            }
            // Division: `/=` or `/`.
            if i + 1 < n && b[i + 1] == b'=' {
                i += 2;
                push!(Tk::Punct(Pk::SlashEq), start, i);
            } else {
                i += 1;
                push!(Tk::Punct(Pk::Slash), start, i);
            }
            regex_state = RegexState::Allowed;
            continue;
        }

        // `}` — may resume a template.
        if c == b'}' {
            if brace_stack.last() == Some(&true) {
                brace_stack.pop();
                let (end, has_sub) = scan_template_piece(b, i + 1)
                    .ok_or_else(|| "unterminated template literal".to_string())?;
                if has_sub {
                    push!(Tk::TemplateMiddle, start, end);
                    brace_stack.push(true);
                    regex_state = RegexState::Allowed;
                } else {
                    push!(Tk::TemplateTail, start, end);
                    regex_state = RegexState::Div;
                }
                i = end;
                continue;
            }
            brace_stack.pop();
            i += 1;
            push!(Tk::Punct(Pk::RBrace), start, i);
            regex_state = RegexState::Div;
            continue;
        }
        if c == b'{' {
            brace_stack.push(false);
            i += 1;
            push!(Tk::Punct(Pk::LBrace), start, i);
            regex_state = RegexState::Allowed;
            continue;
        }

        // Other punctuators.
        let (pk, len) =
            match_punct(b, i).ok_or_else(|| format!("unexpected character {:?}", c as char))?;
        i += len;
        push!(Tk::Punct(pk), start, i);
        // After a value-ending punctuator (`)` `]` `++` `--`), `/` is division.
        regex_state = match pk {
            Pk::RParen | Pk::RBracket | Pk::PlusPlus | Pk::MinusMinus => RegexState::Div,
            _ => RegexState::Allowed,
        };
    }

    out.push(Token { kind: Tk::Eof, start: n, end: n, nl_before: nl_pending });
    Ok(out)
}

fn scan_number(b: &[u8], mut i: usize) -> usize {
    let n = b.len();
    // 0x / 0o / 0b prefixes.
    if b[i] == b'0' && i + 1 < n {
        let p = b[i + 1];
        if matches!(p, b'x' | b'X' | b'o' | b'O' | b'b' | b'B') {
            i += 2;
            while i < n && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            if i < n && b[i] == b'n' {
                i += 1;
            }
            return i;
        }
    }
    while i < n {
        let c = b[i];
        if c.is_ascii_digit() || c == b'_' || c == b'.' {
            i += 1;
        } else if c == b'e' || c == b'E' {
            i += 1;
            if i < n && (b[i] == b'+' || b[i] == b'-') {
                i += 1;
            }
        } else if c == b'n' {
            i += 1;
            break;
        } else {
            break;
        }
    }
    i
}

/// Scan a template piece starting at `i` (just after a `` ` `` or a resuming
/// `}`). Returns (end, has_substitution): `end` is the byte just after the
/// terminating `` ` `` (has_substitution=false) or `${` (has_substitution=true).
fn scan_template_piece(b: &[u8], mut i: usize) -> Option<(usize, bool)> {
    let n = b.len();
    while i < n {
        let c = b[i];
        if c == b'\\' {
            i += 2;
            continue;
        }
        if c == b'`' {
            return Some((i + 1, false));
        }
        if c == b'$' && i + 1 < n && b[i + 1] == b'{' {
            return Some((i + 2, true));
        }
        i += 1;
    }
    None
}

/// Scan a regex literal starting at the leading `/`. Returns end offset.
fn scan_regex(b: &[u8], mut i: usize) -> Option<usize> {
    let n = b.len();
    debug_assert_eq!(b[i], b'/');
    i += 1;
    let mut in_class = false;
    while i < n {
        let c = b[i];
        match c {
            b'\\' => {
                i += 2;
                continue;
            }
            b'\n' | b'\r' => return None,
            b'[' => in_class = true,
            b']' => in_class = false,
            b'/' if !in_class => {
                i += 1;
                // Flags.
                while i < n && is_id_continue(b[i]) {
                    i += 1;
                }
                return Some(i);
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Match a punctuator at `i`, returning (kind, byte length). Assumes the byte
/// is not one already handled (`/`, `{`, `}`, backtick, string quote, digit,
/// id-start).
pub(crate) fn match_punct(b: &[u8], i: usize) -> Option<(Pk, usize)> {
    let n = b.len();
    let at = |k: usize| if i + k < n { b[i + k] } else { 0 };
    let c0 = b[i];
    let c1 = at(1);
    let c2 = at(2);
    let c3 = at(3);
    Some(match c0 {
        b'(' => (Pk::LParen, 1),
        b')' => (Pk::RParen, 1),
        b'[' => (Pk::LBracket, 1),
        b']' => (Pk::RBracket, 1),
        b';' => (Pk::Semi, 1),
        b',' => (Pk::Comma, 1),
        b'~' => (Pk::Tilde, 1),
        b'@' => (Pk::At, 1),
        b'?' => {
            if c1 == b'?' && c2 == b'=' {
                (Pk::QQEq, 3)
            } else if c1 == b'?' {
                (Pk::QQ, 2)
            } else if c1 == b'.' && !c2.is_ascii_digit() {
                (Pk::QDot, 2)
            } else {
                (Pk::Question, 1)
            }
        }
        b':' => (Pk::Colon, 1),
        b'.' => {
            if c1 == b'.' && c2 == b'.' {
                (Pk::Ellipsis, 3)
            } else {
                (Pk::Dot, 1)
            }
        }
        b'<' => {
            if c1 == b'<' && c2 == b'=' {
                (Pk::ShlEq, 3)
            } else if c1 == b'<' {
                (Pk::Shl, 2)
            } else if c1 == b'=' {
                (Pk::Le, 2)
            } else {
                (Pk::Lt, 1)
            }
        }
        b'>' => {
            if c1 == b'>' && c2 == b'>' && c3 == b'=' {
                (Pk::UShrEq, 4)
            } else if c1 == b'>' && c2 == b'>' {
                (Pk::UShr, 3)
            } else if c1 == b'>' && c2 == b'=' {
                (Pk::ShrEq, 3)
            } else if c1 == b'>' {
                (Pk::Shr, 2)
            } else if c1 == b'=' {
                (Pk::Ge, 2)
            } else {
                (Pk::Gt, 1)
            }
        }
        b'=' => {
            if c1 == b'=' && c2 == b'=' {
                (Pk::EqEqEq, 3)
            } else if c1 == b'=' {
                (Pk::EqEq, 2)
            } else if c1 == b'>' {
                (Pk::Arrow, 2)
            } else {
                (Pk::Eq, 1)
            }
        }
        b'!' => {
            if c1 == b'=' && c2 == b'=' {
                (Pk::NotEqEq, 3)
            } else if c1 == b'=' {
                (Pk::NotEq, 2)
            } else {
                (Pk::Bang, 1)
            }
        }
        b'+' => {
            if c1 == b'+' {
                (Pk::PlusPlus, 2)
            } else if c1 == b'=' {
                (Pk::PlusEq, 2)
            } else {
                (Pk::Plus, 1)
            }
        }
        b'-' => {
            if c1 == b'-' {
                (Pk::MinusMinus, 2)
            } else if c1 == b'=' {
                (Pk::MinusEq, 2)
            } else {
                (Pk::Minus, 1)
            }
        }
        b'*' => {
            if c1 == b'*' && c2 == b'=' {
                (Pk::StarStarEq, 3)
            } else if c1 == b'*' {
                (Pk::StarStar, 2)
            } else if c1 == b'=' {
                (Pk::StarEq, 2)
            } else {
                (Pk::Star, 1)
            }
        }
        b'%' => {
            if c1 == b'=' {
                (Pk::PercentEq, 2)
            } else {
                (Pk::Percent, 1)
            }
        }
        b'&' => {
            if c1 == b'&' && c2 == b'=' {
                (Pk::AmpAmpEq, 3)
            } else if c1 == b'&' {
                (Pk::AmpAmp, 2)
            } else if c1 == b'=' {
                (Pk::AmpEq, 2)
            } else {
                (Pk::Amp, 1)
            }
        }
        b'|' => {
            if c1 == b'|' && c2 == b'=' {
                (Pk::PipePipeEq, 3)
            } else if c1 == b'|' {
                (Pk::PipePipe, 2)
            } else if c1 == b'=' {
                (Pk::PipeEq, 2)
            } else {
                (Pk::Pipe, 1)
            }
        }
        b'^' => {
            if c1 == b'=' {
                (Pk::CaretEq, 2)
            } else {
                (Pk::Caret, 1)
            }
        }
        _ => return None,
    })
}
