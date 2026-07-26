//! Pattern parser: the ES2025 §22.2.1 *main* grammar, exactly.
//!
//! Classification discipline (THE BAR): in `u`/`v` mode every parse error is
//! `Syntax` (Annex B does not apply). In non-Unicode mode a construct that
//! Annex B (or any extension) might accept is refused as `Unsupported`;
//! `Syntax` is returned only where BOTH grammars reject (verified against
//! the reference engine: unterminated groups/classes, reversed char ranges,
//! `a{2,1}`, quantified non-lookahead assertions, `a**`, bad group names,
//! bad modifier lists, `\k<undefined>` when named groups exist, dangling
//! `\`, unmatched `)`, …). A `Syntax` verdict from this parser therefore
//! always means "a conforming engine throws SyntaxError".
//!
//! Author: Andrew Yates
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::ast::*;
use crate::generated::emoji_strings::string_property;
use crate::generated::gc_tables::gc_ranges;
use crate::generated::property_tables::{binary_property, P_ID_CONTINUE, P_ID_START};
use crate::generated::script_tables::{script_ext_ranges, script_ranges};
use crate::unicode::{self, in_ranges};
use crate::{CompileError, Flags};

/// Sound refusal bound: recursion in parse/compile/drop must stay well
/// within a 2 MiB thread stack. Real-world patterns nest far shallower;
/// engines that accept deeper nesting are not contradicted by a refusal.
const MAX_DEPTH: u32 = 100;
/// Quantifier bounds at or above 2^32 are refused (engines clamp; we do not
/// approximate).
const MAX_QUANT: u64 = u32::MAX as u64;
/// The spec has no capture limit; refuse resource-extreme counts soundly.
const MAX_GROUPS: u32 = 100_000;

pub(crate) fn parse(src: &[u16], flags: Flags) -> Result<Parsed, CompileError> {
    let mut p = Parser {
        src,
        pos: 0,
        unicode: flags.has_either_unicode(),
        v: flags.unicode_sets,
        n_groups: 0,
        group_names: Vec::new(),
        disj_counter: 0,
        path: Vec::new(),
        depth: 0,
    };
    let mut root = p.parse_disjunction()?;
    if p.pos < p.src.len() {
        // The only way the disjunction stops early is an unmatched ')'.
        return Err(p.syntax("unmatched ')'"));
    }
    p.check_duplicate_names()?;
    p.resolve_refs(&mut root)?;
    Ok(Parsed {
        root,
        n_groups: p.n_groups,
        group_names: p.group_names,
    })
}

struct Parser<'a> {
    src: &'a [u16],
    pos: usize,
    unicode: bool,
    v: bool,
    n_groups: u32,
    group_names: Vec<GroupName>,
    disj_counter: u32,
    path: Vec<(u32, u32)>,
    depth: u32,
}

enum EscOut {
    Ch(u32),
    Cls(EscClass),
    Backref(u32),
    NamedRef(String),
}

#[derive(PartialEq, Clone, Copy)]
enum EscCtx {
    Top,
    ClassSimple,
    ClassV,
}

fn is_syntax_char(c: u32) -> bool {
    matches!(
        c,
        0x5E | 0x24 | 0x5C | 0x2E | 0x2A | 0x2B | 0x3F | 0x28 | 0x29 | 0x5B | 0x5D | 0x7B
            | 0x7D | 0x7C
    ) // ^ $ \ . * + ? ( ) [ ] { } |
}

/// ClassSetReservedPunctuator (v-mode).
fn is_v_reserved_punct(c: u32) -> bool {
    matches!(c as u8 as char, '&' | '-' | '!' | '#' | '%' | ',' | ':' | ';' | '<' | '=' | '>'
        | '@' | '`' | '~') && c < 0x80
}

/// First char of a ClassSetReservedDoublePunctuator pair.
fn is_v_double_punct(c: u32) -> bool {
    matches!(c as u8 as char, '&' | '!' | '#' | '$' | '%' | '*' | '+' | ',' | '.' | ':' | ';'
        | '<' | '=' | '>' | '?' | '@' | '^' | '`' | '~') && c < 0x80
}

/// ClassSetSyntaxCharacter (v-mode): never a literal.
fn is_v_syntax_char(c: u32) -> bool {
    matches!(c as u8 as char, '(' | ')' | '[' | ']' | '{' | '}' | '/' | '-' | '\\' | '|')
        && c < 0x80
}

fn is_id_start_cp(c: u32) -> bool {
    c == 0x24 || c == 0x5F || in_ranges(P_ID_START, c) // $ _ ID_Start
}

fn is_id_continue_cp(c: u32) -> bool {
    c == 0x24 || c == 0x200C || c == 0x200D || in_ranges(P_ID_CONTINUE, c) // $ ZWNJ ZWJ
}

impl<'a> Parser<'a> {
    // -- errors ------------------------------------------------------------

    /// Invalid in BOTH the main grammar and Annex B: a real SyntaxError.
    fn syntax(&self, msg: &str) -> CompileError {
        CompileError::Syntax(msg.to_string())
    }

    /// Invalid in the main grammar; Annex B (non-Unicode mode) accepts it or
    /// might: Syntax under u/v, a sound refusal otherwise.
    fn lax(&self, msg: &str) -> CompileError {
        if self.unicode {
            CompileError::Syntax(msg.to_string())
        } else {
            CompileError::Unsupported(format!("annex-b-only construct: {msg}"))
        }
    }

    fn unsupported(&self, msg: &str) -> CompileError {
        CompileError::Unsupported(msg.to_string())
    }

    // -- reading -----------------------------------------------------------

    fn cur(&self) -> Option<u32> {
        if self.pos >= self.src.len() {
            None
        } else {
            Some(unicode::read_forward(self.src, self.pos, self.unicode).0)
        }
    }

    /// The character after the current one.
    fn peek2(&self) -> Option<u32> {
        if self.pos >= self.src.len() {
            return None;
        }
        let w = unicode::read_forward(self.src, self.pos, self.unicode).1;
        if self.pos + w >= self.src.len() {
            None
        } else {
            Some(unicode::read_forward(self.src, self.pos + w, self.unicode).0)
        }
    }

    fn bump(&mut self) {
        self.pos += unicode::read_forward(self.src, self.pos, self.unicode).1;
    }

    fn eat(&mut self, c: u32) -> bool {
        if self.cur() == Some(c) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn eat_ascii(&mut self, c: char) -> bool {
        self.eat(c as u32)
    }

    fn at_seq(&self, a: char, b: char) -> bool {
        self.cur() == Some(a as u32) && self.peek2() == Some(b as u32)
    }

    // -- disjunction / alternative / term ---------------------------------

    fn parse_disjunction(&mut self) -> Result<Node, CompileError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(self.unsupported("pattern nesting too deep"));
        }
        let id = self.disj_counter;
        self.disj_counter += 1;
        self.path.push((id, 0));
        let mut alts = vec![self.parse_alternative()?];
        while self.eat_ascii('|') {
            let alt_idx = alts.len() as u32;
            self.path.last_mut().unwrap().1 = alt_idx;
            alts.push(self.parse_alternative()?);
        }
        self.path.pop();
        self.depth -= 1;
        Ok(if alts.len() == 1 {
            alts.pop().unwrap()
        } else {
            Node::Alternation(alts)
        })
    }

    fn parse_alternative(&mut self) -> Result<Node, CompileError> {
        let mut terms = Vec::new();
        loop {
            match self.cur() {
                None => break,
                Some(c) if c == '|' as u32 || c == ')' as u32 => break,
                _ => terms.push(self.parse_term()?),
            }
        }
        Ok(match terms.len() {
            0 => Node::Empty,
            1 => terms.pop().unwrap(),
            _ => Node::Concat(terms),
        })
    }

    fn parse_term(&mut self) -> Result<Node, CompileError> {
        let c = self.cur().unwrap();
        match c as u8 as char {
            '^' if c < 0x80 => {
                self.bump();
                self.no_quantifier_after_assertion("^")?;
                Ok(Node::LineStart)
            }
            '$' if c < 0x80 => {
                self.bump();
                self.no_quantifier_after_assertion("$")?;
                Ok(Node::LineEnd)
            }
            '\\' if c < 0x80 => {
                // \b \B assertions are terms, not atom escapes.
                match self.peek2() {
                    Some(n) if n == 'b' as u32 => {
                        self.bump();
                        self.bump();
                        self.no_quantifier_after_assertion("\\b")?;
                        return Ok(Node::WordBoundary { negate: false });
                    }
                    Some(n) if n == 'B' as u32 => {
                        self.bump();
                        self.bump();
                        self.no_quantifier_after_assertion("\\B")?;
                        return Ok(Node::WordBoundary { negate: true });
                    }
                    _ => {}
                }
                self.bump(); // consume '\'
                let atom = match self.parse_escape(EscCtx::Top)? {
                    EscOut::Ch(cp) => Node::Literal(cp),
                    // In v mode a top-level class escape follows the v-mode
                    // set semantics (fold-at-operand, fixed-universe
                    // complement, properties of strings).
                    EscOut::Cls(e) if self.v => Node::Class(ClassAst::VMode {
                        negate: false,
                        expr: VExpr::Union(vec![VOperand::Esc(e)]),
                    }),
                    EscOut::Cls(e) => Node::Class(ClassAst::Simple {
                        negate: false,
                        items: vec![ClassItem::Esc(e)],
                    }),
                    EscOut::Backref(n) => Node::Backref(n),
                    EscOut::NamedRef(name) => Node::NamedBackrefRaw(name),
                };
                self.maybe_quantify(atom)
            }
            '(' if c < 0x80 => self.parse_group(),
            '[' if c < 0x80 => {
                self.bump();
                let cls = if self.v {
                    self.parse_vclass()?
                } else {
                    self.parse_simple_class()?
                };
                self.maybe_quantify(Node::Class(cls))
            }
            '.' if c < 0x80 => {
                self.bump();
                self.maybe_quantify(Node::Dot)
            }
            '*' | '+' | '?' if c < 0x80 => Err(self.syntax("nothing to repeat")),
            '{' if c < 0x80 => {
                let save = self.pos;
                if self.try_parse_braced_quantifier()?.is_some() {
                    // A valid braced quantifier with nothing to repeat is a
                    // SyntaxError under Annex B as well.
                    return Err(self.syntax("nothing to repeat"));
                }
                self.pos = save;
                Err(self.lax("literal '{' outside a quantifier"))
            }
            '}' if c < 0x80 => Err(self.lax("lone '}'")),
            ']' if c < 0x80 => Err(self.lax("lone ']'")),
            _ => {
                self.bump();
                self.maybe_quantify(Node::Literal(c))
            }
        }
    }

    /// `^ $ \b \B` (and lookbehind, checked at the call site) may not be
    /// quantified — a SyntaxError in both grammars.
    fn no_quantifier_after_assertion(&mut self, what: &str) -> Result<(), CompileError> {
        let save = self.pos;
        if self.parse_quantifier_opt()?.is_some() {
            return Err(self.syntax(&format!("quantifier after assertion {what}")));
        }
        self.pos = save;
        Ok(())
    }

    fn maybe_quantify(&mut self, atom: Node) -> Result<Node, CompileError> {
        match self.parse_quantifier_opt()? {
            Some((min, max, greedy)) => Ok(Node::Quant {
                min,
                max,
                greedy,
                body: Box::new(atom),
            }),
            None => Ok(atom),
        }
    }

    /// Parse a quantifier if present. Returns (min, max, greedy);
    /// max == u64::MAX means unbounded.
    fn parse_quantifier_opt(&mut self) -> Result<Option<(u64, u64, bool)>, CompileError> {
        let (min, max) = match self.cur() {
            Some(c) if c == '*' as u32 => {
                self.bump();
                (0, u64::MAX)
            }
            Some(c) if c == '+' as u32 => {
                self.bump();
                (1, u64::MAX)
            }
            Some(c) if c == '?' as u32 => {
                self.bump();
                (0, 1)
            }
            Some(c) if c == '{' as u32 => {
                let save = self.pos;
                match self.try_parse_braced_quantifier()? {
                    Some(mm) => mm,
                    None => {
                        self.pos = save;
                        return Ok(None);
                    }
                }
            }
            _ => return Ok(None),
        };
        let greedy = !self.eat_ascii('?');
        Ok(Some((min, max, greedy)))
    }

    /// Try `{ n }` / `{ n , }` / `{ n , m }` from the current `{`. On shape
    /// mismatch returns None with the position unspecified (caller restores).
    /// `{n,m}` with n > m is a SyntaxError in both grammars.
    fn try_parse_braced_quantifier(&mut self) -> Result<Option<(u64, u64)>, CompileError> {
        debug_assert_eq!(self.cur(), Some('{' as u32));
        self.bump();
        let Some(min) = self.read_decimal() else {
            return Ok(None);
        };
        if self.eat_ascii('}') {
            if min > MAX_QUANT {
                return Err(self.unsupported("quantifier bound >= 2^32"));
            }
            return Ok(Some((min, min)));
        }
        if !self.eat_ascii(',') {
            return Ok(None);
        }
        if min > MAX_QUANT {
            return Err(self.unsupported("quantifier bound >= 2^32"));
        }
        if self.eat_ascii('}') {
            return Ok(Some((min, u64::MAX)));
        }
        let Some(max) = self.read_decimal() else {
            return Ok(None);
        };
        if !self.eat_ascii('}') {
            return Ok(None);
        }
        if min > max {
            return Err(self.syntax("numbers out of order in {} quantifier"));
        }
        if max > MAX_QUANT {
            // Engines clamp huge bounds; we refuse rather than approximate.
            return Err(self.unsupported("quantifier bound >= 2^32"));
        }
        Ok(Some((min, max)))
    }

    fn read_decimal(&mut self) -> Option<u64> {
        let mut any = false;
        let mut v: u64 = 0;
        while let Some(c) = self.cur() {
            if !(0x30..=0x39).contains(&c) {
                break;
            }
            any = true;
            v = v.saturating_mul(10).saturating_add((c - 0x30) as u64);
            self.bump();
        }
        if any { Some(v) } else { None }
    }

    // -- groups ------------------------------------------------------------

    fn parse_group(&mut self) -> Result<Node, CompileError> {
        self.bump(); // '('
        if !self.eat_ascii('?') {
            let index = self.next_group_index()?;
            let body = self.parse_disjunction()?;
            self.expect_close_paren()?;
            return self.maybe_quantify(Node::Group {
                index,
                body: Box::new(body),
            });
        }
        // Match on the full code point, NOT `c as u8 as char`: a truncating
        // low-byte compare would misroute a non-ASCII first char whose low
        // byte collides with an ASCII marker. Notably the dog-emoji lead
        // surrogate U+D83D truncates to 0x3D ('='), so `(?<🐕>…)` would be
        // read as a lookbehind `(?<=…)` and a bad group name wrongly accepted.
        match self.cur() {
            Some(c) if c == ':' as u32 => {
                self.bump();
                let body = self.parse_disjunction()?;
                self.expect_close_paren()?;
                self.maybe_quantify(Node::NonCapGroup(Box::new(body)))
            }
            Some(c) if c == '=' as u32 || c == '!' as u32 => {
                let negative = self.cur() == Some('!' as u32);
                self.bump();
                let body = self.parse_disjunction()?;
                self.expect_close_paren()?;
                let node = Node::Look {
                    behind: false,
                    negative,
                    body: Box::new(body),
                };
                // Annex B: lookahead is quantifiable in non-Unicode mode.
                let save = self.pos;
                if self.parse_quantifier_opt()?.is_some() {
                    return Err(self.lax("quantified lookahead"));
                }
                self.pos = save;
                Ok(node)
            }
            Some(c) if c == '<' as u32 => {
                self.bump();
                match self.cur() {
                    Some(c) if c == '=' as u32 || c == '!' as u32 => {
                        let negative = self.cur() == Some('!' as u32);
                        self.bump();
                        let body = self.parse_disjunction()?;
                        self.expect_close_paren()?;
                        // Lookbehind is never quantifiable (both grammars).
                        let save = self.pos;
                        if self.parse_quantifier_opt()?.is_some() {
                            return Err(self.syntax("quantified lookbehind"));
                        }
                        self.pos = save;
                        Ok(Node::Look {
                            behind: true,
                            negative,
                            body: Box::new(body),
                        })
                    }
                    _ => {
                        // Named capturing group; bad names are SyntaxErrors
                        // in both grammars.
                        let name = self.parse_group_name(true)?;
                        let index = self.next_group_index()?;
                        self.group_names.push(GroupName {
                            name,
                            index,
                            path: self.path.clone(),
                        });
                        let body = self.parse_disjunction()?;
                        self.expect_close_paren()?;
                        self.maybe_quantify(Node::Group {
                            index,
                            body: Box::new(body),
                        })
                    }
                }
            }
            Some(c) if c < 0x80 && matches!(c as u8 as char, 'i' | 'm' | 's' | '-') => {
                self.parse_mod_group()
            }
            _ => Err(self.syntax("invalid group")),
        }
    }

    fn parse_mod_group(&mut self) -> Result<Node, CompileError> {
        let add = self.parse_mod_list()?;
        let mut remove = ModFlags::default();
        let has_minus = self.eat_ascii('-');
        if has_minus {
            remove = self.parse_mod_list()?;
        }
        if !self.eat_ascii(':') {
            return Err(self.syntax("invalid regular expression modifiers"));
        }
        // Syntax Error only when BOTH modifier lists are empty; `(?ims-:…)`
        // and `(?-i:…)` are valid.
        let none = |f: ModFlags| !f.i && !f.m && !f.s;
        if none(add) && (!has_minus || none(remove)) {
            return Err(self.syntax("empty regular expression modifiers"));
        }
        if (add.i && remove.i) || (add.m && remove.m) || (add.s && remove.s) {
            return Err(self.syntax("modifier appears in both lists"));
        }
        let body = self.parse_disjunction()?;
        self.expect_close_paren()?;
        self.maybe_quantify(Node::ModGroup {
            add,
            remove,
            body: Box::new(body),
        })
    }

    fn parse_mod_list(&mut self) -> Result<ModFlags, CompileError> {
        let mut f = ModFlags::default();
        loop {
            // Full code-point compare (not truncating `as u8`): a non-ASCII
            // code point whose low byte is 'i'/'m'/'s' must not read as a flag.
            let slot = match self.cur() {
                Some(c) if c == 'i' as u32 => &mut f.i,
                Some(c) if c == 'm' as u32 => &mut f.m,
                Some(c) if c == 's' as u32 => &mut f.s,
                _ => return Ok(f),
            };
            if *slot {
                return Err(self.syntax("repeated regular expression modifier"));
            }
            *slot = true;
            self.bump();
        }
    }

    fn next_group_index(&mut self) -> Result<u32, CompileError> {
        self.n_groups += 1;
        if self.n_groups > MAX_GROUPS {
            return Err(self.unsupported("too many capturing groups"));
        }
        Ok(self.n_groups)
    }

    fn expect_close_paren(&mut self) -> Result<(), CompileError> {
        if self.eat_ascii(')') {
            Ok(())
        } else {
            Err(self.syntax("unterminated group"))
        }
    }

    // -- escapes -----------------------------------------------------------

    /// Parse an escape body (the `\` is already consumed).
    fn parse_escape(&mut self, ctx: EscCtx) -> Result<EscOut, CompileError> {
        let Some(c) = self.cur() else {
            return Err(self.syntax("pattern may not end with a trailing backslash"));
        };
        match c as u8 as char {
            't' if c < 0x80 => {
                self.bump();
                Ok(EscOut::Ch(0x09))
            }
            'n' if c < 0x80 => {
                self.bump();
                Ok(EscOut::Ch(0x0A))
            }
            'v' if c < 0x80 => {
                self.bump();
                Ok(EscOut::Ch(0x0B))
            }
            'f' if c < 0x80 => {
                self.bump();
                Ok(EscOut::Ch(0x0C))
            }
            'r' if c < 0x80 => {
                self.bump();
                Ok(EscOut::Ch(0x0D))
            }
            'd' | 'D' if c < 0x80 => {
                self.bump();
                Ok(EscOut::Cls(EscClass::Digit { negate: c == 'D' as u32 }))
            }
            's' | 'S' if c < 0x80 => {
                self.bump();
                Ok(EscOut::Cls(EscClass::Space { negate: c == 'S' as u32 }))
            }
            'w' | 'W' if c < 0x80 => {
                self.bump();
                Ok(EscOut::Cls(EscClass::Word { negate: c == 'W' as u32 }))
            }
            'p' | 'P' if c < 0x80 => {
                if !self.unicode {
                    return Err(self.unsupported("annex-b-only construct: identity escape \\p"));
                }
                self.bump();
                self.parse_property(c == 'P' as u32)
            }
            'c' if c < 0x80 => {
                match self.peek2() {
                    Some(l) if (0x41..=0x5A).contains(&l) || (0x61..=0x7A).contains(&l) => {
                        self.bump();
                        self.bump();
                        Ok(EscOut::Ch(l % 32))
                    }
                    _ => Err(self.lax("\\c must be followed by a control letter")),
                }
            }
            '0' if c < 0x80 => {
                self.bump();
                match self.cur() {
                    Some(d) if (0x30..=0x39).contains(&d) => {
                        Err(self.lax("legacy octal escape"))
                    }
                    _ => Ok(EscOut::Ch(0)),
                }
            }
            '1'..='9' if c < 0x80 => {
                if ctx == EscCtx::Top {
                    let n = self.read_decimal().unwrap();
                    // Validated against the group count post-parse.
                    Ok(EscOut::Backref(n.min(u32::MAX as u64) as u32))
                } else {
                    Err(self.lax("decimal escape in character class"))
                }
            }
            'x' if c < 0x80 => {
                self.bump();
                match self.read_hex(2) {
                    Some(v) => Ok(EscOut::Ch(v)),
                    None => Err(self.lax("invalid \\x escape")),
                }
            }
            'u' if c < 0x80 => {
                self.bump();
                match self.parse_unicode_escape_body(self.unicode) {
                    Some(cp) => Ok(EscOut::Ch(cp)),
                    None => Err(self.lax("invalid unicode escape")),
                }
            }
            'k' if c < 0x80 && ctx == EscCtx::Top => {
                self.bump();
                if self.cur() == Some('<' as u32) {
                    self.bump();
                    // A malformed name here: Syntax under u/v; under
                    // non-Unicode Annex B may reparse \k as identity.
                    let name = self.parse_group_name(self.unicode)?;
                    Ok(EscOut::NamedRef(name))
                } else {
                    Err(self.lax("\\k must reference a named group"))
                }
            }
            'b' if c < 0x80 && ctx != EscCtx::Top => {
                self.bump();
                Ok(EscOut::Ch(0x08))
            }
            _ => self.parse_identity_escape(ctx, c),
        }
    }

    fn parse_identity_escape(&mut self, ctx: EscCtx, c: u32) -> Result<EscOut, CompileError> {
        if self.unicode {
            let ok = is_syntax_char(c)
                || c == '/' as u32
                || (ctx == EscCtx::ClassSimple && c == '-' as u32)
                || (ctx == EscCtx::ClassV && is_v_reserved_punct(c));
            if ok {
                self.bump();
                Ok(EscOut::Ch(c))
            } else {
                Err(self.syntax("invalid identity escape"))
            }
        } else {
            // Main grammar: IdentityEscape :: SourceCharacter but not
            // UnicodeIDContinue. Annex B accepts nearly everything else.
            if in_ranges(P_ID_CONTINUE, c) {
                Err(self.unsupported("annex-b-only construct: identity escape of ID_Continue char"))
            } else {
                self.bump();
                Ok(EscOut::Ch(c))
            }
        }
    }

    /// `\u` escape body (the `u` is consumed). None = not a valid escape.
    /// `full` enables the u-mode forms (`\u{…}` and surrogate-pair joins);
    /// group names always use the full grammar.
    fn parse_unicode_escape_body(&mut self, full: bool) -> Option<u32> {
        if full && self.cur() == Some('{' as u32) {
            self.bump();
            let mut v: u32 = 0;
            let mut any = false;
            while let Some(c) = self.cur() {
                let Some(d) = hex_val(c) else { break };
                any = true;
                v = v.saturating_mul(16).saturating_add(d);
                if v > 0x10FFFF {
                    return None;
                }
                self.bump();
            }
            if !any || !self.eat_ascii('}') {
                return None;
            }
            return Some(v);
        }
        let lead = self.read_hex(4)?;
        if full && (0xD800..=0xDBFF).contains(&lead) {
            // u HexLeadSurrogate \u HexTrailSurrogate joins into one cp.
            let save = self.pos;
            if self.eat_ascii('\\') && self.eat_ascii('u') {
                if let Some(trail) = self.read_hex(4) {
                    if (0xDC00..=0xDFFF).contains(&trail) {
                        return Some(unicode::combine(lead as u16, trail as u16));
                    }
                }
            }
            self.pos = save;
        }
        Some(lead)
    }

    fn read_hex(&mut self, n: usize) -> Option<u32> {
        let save = self.pos;
        let mut v = 0;
        for _ in 0..n {
            let d = self.cur().and_then(hex_val);
            match d {
                Some(d) => {
                    v = v * 16 + d;
                    self.bump();
                }
                None => {
                    self.pos = save;
                    return None;
                }
            }
        }
        Some(v)
    }

    /// `\p{…}` / `\P{…}` (u/v modes only; the `p`/`P` is consumed).
    fn parse_property(&mut self, negate: bool) -> Result<EscOut, CompileError> {
        if !self.eat_ascii('{') {
            return Err(self.syntax("\\p must be followed by {property}"));
        }
        let name = self.read_prop_word();
        if self.eat_ascii('=') {
            let value = self.read_prop_word();
            let chars: &'static [(u32, u32)] = match name.as_str() {
                "General_Category" | "gc" => gc_ranges(&value),
                "Script" | "sc" => script_ranges(&value),
                "Script_Extensions" | "scx" => script_ext_ranges(&value),
                _ => None,
            }
            .ok_or_else(|| self.syntax("invalid property name/value"))?;
            if !self.eat_ascii('}') {
                return Err(self.syntax("unterminated \\p{...}"));
            }
            return Ok(EscOut::Cls(EscClass::Property {
                negate,
                chars,
                strings: &[],
            }));
        }
        if !self.eat_ascii('}') {
            return Err(self.syntax("unterminated \\p{...}"));
        }
        if let Some(chars) = binary_property(&name).or_else(|| gc_ranges(&name)) {
            return Ok(EscOut::Cls(EscClass::Property {
                negate,
                chars,
                strings: &[],
            }));
        }
        if self.v {
            if let Some((chars, strings)) = string_property(&name) {
                if negate {
                    return Err(self.syntax("\\P cannot name a property of strings"));
                }
                return Ok(EscOut::Cls(EscClass::Property {
                    negate: false,
                    chars,
                    strings,
                }));
            }
        }
        Err(self.syntax("invalid property name"))
    }

    fn read_prop_word(&mut self) -> String {
        let mut s = String::new();
        while let Some(c) = self.cur() {
            let ok = (0x30..=0x39).contains(&c)
                || (0x41..=0x5A).contains(&c)
                || (0x61..=0x7A).contains(&c)
                || c == 0x5F;
            if !ok {
                break;
            }
            s.push(c as u8 as char);
            self.bump();
        }
        s
    }

    // -- group names -------------------------------------------------------

    /// After `(?<` or `\k<`: parse `Name>`; `strict` = errors are Syntax
    /// (group definitions and u-mode `\k`), else the Annex-B refusal lane.
    fn parse_group_name(&mut self, strict: bool) -> Result<String, CompileError> {
        let mut name = String::new();
        let mut first = true;
        loop {
            if self.eat_ascii('>') {
                if name.is_empty() {
                    return Err(self.name_err(strict, "empty group name"));
                }
                return Ok(name);
            }
            let Some(cp) = self.read_name_char(strict)? else {
                return Err(self.name_err(strict, "invalid group name"));
            };
            let ok = if first {
                is_id_start_cp(cp)
            } else {
                is_id_continue_cp(cp)
            };
            if !ok {
                return Err(self.name_err(strict, "invalid group name character"));
            }
            name.push(char::from_u32(cp).ok_or_else(|| self.syntax("invalid group name"))?);
            first = false;
        }
    }

    fn name_err(&self, strict: bool, msg: &str) -> CompileError {
        if strict {
            self.syntax(msg)
        } else {
            self.lax(msg)
        }
    }

    /// One RegExpIdentifierName character: a `\u` escape (always full
    /// grammar) or a source character (surrogate pairs join in all modes).
    fn read_name_char(&mut self, strict: bool) -> Result<Option<u32>, CompileError> {
        if self.pos >= self.src.len() {
            return Ok(None);
        }
        if self.src[self.pos] == '\\' as u16 {
            self.pos += 1;
            if !self.eat_ascii('u') {
                return Err(self.name_err(strict, "bad escape in group name"));
            }
            match self.parse_unicode_escape_body(true) {
                Some(cp) => return Ok(Some(cp)),
                None => return Err(self.name_err(strict, "bad unicode escape in group name")),
            }
        }
        // Raw source char: join surrogate pairs regardless of mode.
        let (cp, w) = unicode::read_forward(self.src, self.pos, true);
        self.pos += w;
        Ok(Some(cp))
    }

    // -- character classes (non-v) ----------------------------------------

    fn parse_simple_class(&mut self) -> Result<ClassAst, CompileError> {
        let negate = self.eat_ascii('^');
        let mut items = Vec::new();
        loop {
            match self.cur() {
                None => return Err(self.syntax("unterminated character class")),
                Some(c) if c == ']' as u32 => {
                    self.bump();
                    return Ok(ClassAst::Simple { negate, items });
                }
                _ => {}
            }
            let a = self.parse_class_atom()?;
            // Range if '-' follows and is not the class-final '-]'.
            if self.cur() == Some('-' as u32) && self.peek2().is_some_and(|n| n != ']' as u32) {
                self.bump(); // '-'
                let b = self.parse_class_atom()?;
                match (a, b) {
                    (CAtom::Ch(lo), CAtom::Ch(hi)) => {
                        if lo > hi {
                            return Err(self.syntax("range out of order in character class"));
                        }
                        items.push(ClassItem::Range(lo, hi));
                    }
                    _ => {
                        // A class escape as a range bound: Annex B demotes
                        // the '-' to a literal; the main grammar rejects.
                        return Err(self.lax("character class escape as range bound"));
                    }
                }
            } else {
                items.push(match a {
                    CAtom::Ch(cp) => ClassItem::Char(cp),
                    CAtom::Esc(e) => ClassItem::Esc(e),
                });
            }
        }
    }

    fn parse_class_atom(&mut self) -> Result<CAtom, CompileError> {
        let c = self.cur().ok_or_else(|| self.syntax("unterminated character class"))?;
        if c == '\\' as u32 {
            self.bump();
            match self.parse_escape(EscCtx::ClassSimple)? {
                EscOut::Ch(cp) => Ok(CAtom::Ch(cp)),
                EscOut::Cls(e) => Ok(CAtom::Esc(e)),
                _ => unreachable!("backrefs are not class escapes"),
            }
        } else {
            self.bump();
            Ok(CAtom::Ch(c))
        }
    }

    // -- character classes (v) --------------------------------------------

    fn parse_vclass(&mut self) -> Result<ClassAst, CompileError> {
        let negate = self.eat_ascii('^');
        let expr = self.parse_vexpr()?;
        if !self.eat_ascii(']') {
            return Err(self.syntax("unterminated character class"));
        }
        if negate && expr.may_contain_strings() {
            return Err(self.syntax("negated character class may contain strings"));
        }
        Ok(ClassAst::VMode { negate, expr })
    }

    fn parse_vexpr(&mut self) -> Result<VExpr, CompileError> {
        if self.cur() == Some(']' as u32) {
            return Ok(VExpr::Union(Vec::new()));
        }
        let first = self.parse_v_element()?;
        if self.at_seq('&', '&') {
            let VElement::Op(op) = first else {
                return Err(self.syntax("range operand in class intersection"));
            };
            let mut ops = vec![op];
            while self.at_seq('&', '&') {
                self.bump();
                self.bump();
                if self.cur() == Some('&' as u32) {
                    return Err(self.syntax("invalid '&&&' in character class"));
                }
                ops.push(self.parse_v_operand()?);
            }
            if self.cur() != Some(']' as u32) {
                return Err(self.syntax("mixed class set operators"));
            }
            return Ok(VExpr::Intersection(ops));
        }
        if self.at_seq('-', '-') {
            let VElement::Op(op) = first else {
                return Err(self.syntax("range operand in class subtraction"));
            };
            let mut ops = vec![op];
            while self.at_seq('-', '-') {
                self.bump();
                self.bump();
                ops.push(self.parse_v_operand()?);
            }
            if self.cur() != Some(']' as u32) {
                return Err(self.syntax("mixed class set operators"));
            }
            return Ok(VExpr::Subtraction(ops));
        }
        // Union of juxtaposed elements.
        let mut ops = vec![first.into_operand()];
        while let Some(c) = self.cur() {
            if c == ']' as u32 {
                break;
            }
            ops.push(self.parse_v_element()?.into_operand());
        }
        Ok(VExpr::Union(ops))
    }

    fn parse_v_element(&mut self) -> Result<VElement, CompileError> {
        let op = self.parse_v_operand()?;
        if let VOperand::Char(lo) = op {
            if self.cur() == Some('-' as u32) && self.peek2() != Some('-' as u32) {
                self.bump(); // '-'
                let hi = self.parse_v_range_end()?;
                if lo > hi {
                    return Err(self.syntax("range out of order in character class"));
                }
                return Ok(VElement::Range(lo, hi));
            }
        }
        Ok(VElement::Op(op))
    }

    /// The right endpoint of a v-mode range: must be a ClassSetCharacter.
    fn parse_v_range_end(&mut self) -> Result<u32, CompileError> {
        match self.parse_v_operand()? {
            VOperand::Char(c) => Ok(c),
            _ => Err(self.syntax("invalid character class range endpoint")),
        }
    }

    fn parse_v_operand(&mut self) -> Result<VOperand, CompileError> {
        let Some(c) = self.cur() else {
            return Err(self.syntax("unterminated character class"));
        };
        if c == '[' as u32 {
            self.bump();
            let ClassAst::VMode { negate, expr } = self.parse_vclass()? else {
                unreachable!()
            };
            return Ok(VOperand::Nested {
                negate,
                expr: Box::new(expr),
            });
        }
        if c == '\\' as u32 {
            if self.peek2() == Some('q' as u32) {
                self.bump();
                self.bump();
                return self.parse_string_disjunction();
            }
            self.bump();
            return match self.parse_escape(EscCtx::ClassV)? {
                EscOut::Ch(cp) => Ok(VOperand::Char(cp)),
                EscOut::Cls(e) => Ok(VOperand::Esc(e)),
                _ => unreachable!("backrefs are not class escapes"),
            };
        }
        if is_v_double_punct(c) && self.peek2() == Some(c) {
            return Err(self.syntax("reserved double punctuator in character class"));
        }
        if is_v_syntax_char(c) {
            return Err(self.syntax("invalid character in v-mode character class"));
        }
        self.bump();
        Ok(VOperand::Char(c))
    }

    /// `\q{ ClassString (| ClassString)* }` — the `\q` is consumed.
    fn parse_string_disjunction(&mut self) -> Result<VOperand, CompileError> {
        if !self.eat_ascii('{') {
            return Err(self.syntax("\\q must be followed by {…}"));
        }
        let mut strings = vec![Vec::new()];
        loop {
            match self.cur() {
                None => return Err(self.syntax("unterminated \\q{…}")),
                Some(c) if c == '}' as u32 => {
                    self.bump();
                    return Ok(VOperand::Strings(strings));
                }
                Some(c) if c == '|' as u32 => {
                    self.bump();
                    strings.push(Vec::new());
                }
                Some(c) => {
                    let cp = if c == '\\' as u32 {
                        self.bump();
                        match self.parse_escape(EscCtx::ClassV)? {
                            EscOut::Ch(cp) => cp,
                            _ => return Err(self.syntax("class escape inside \\q{…}")),
                        }
                    } else {
                        if is_v_double_punct(c) && self.peek2() == Some(c) {
                            return Err(self.syntax("reserved double punctuator in \\q{…}"));
                        }
                        if is_v_syntax_char(c) {
                            return Err(self.syntax("invalid character in \\q{…}"));
                        }
                        self.bump();
                        c
                    };
                    strings.last_mut().unwrap().push(cp);
                }
            }
        }
    }

    // -- post-parse resolution --------------------------------------------

    /// ES2025 duplicate-name rule: two groups may share a name only if they
    /// cannot both participate — i.e. some common Disjunction has them in
    /// different Alternatives.
    fn check_duplicate_names(&self) -> Result<(), CompileError> {
        for (i, a) in self.group_names.iter().enumerate() {
            for b in &self.group_names[i + 1..] {
                if a.name != b.name {
                    continue;
                }
                let disjoint = a
                    .path
                    .iter()
                    .zip(b.path.iter())
                    .any(|(x, y)| x.0 == y.0 && x.1 != y.1);
                if !disjoint {
                    return Err(self.syntax("duplicate capture group name"));
                }
            }
        }
        Ok(())
    }

    fn resolve_refs(&self, node: &mut Node) -> Result<(), CompileError> {
        match node {
            Node::Backref(n) => {
                if *n > self.n_groups {
                    // Annex B reparses overflowing \N as a legacy octal.
                    return Err(self.lax("backreference to nonexistent group"));
                }
            }
            Node::NamedBackrefRaw(name) => {
                let groups: Vec<u32> = self
                    .group_names
                    .iter()
                    .filter(|g| g.name == *name)
                    .map(|g| g.index)
                    .collect();
                if groups.is_empty() {
                    return Err(if self.group_names.is_empty() && !self.unicode {
                        // Annex B: with no named groups at all, \k is an
                        // identity escape and the pattern reparses.
                        self.unsupported(
                            "annex-b-only construct: \\k in a pattern without named groups",
                        )
                    } else {
                        self.syntax("backreference to undefined named group")
                    });
                }
                *node = Node::NamedBackref(groups);
            }
            Node::Alternation(xs) | Node::Concat(xs) => {
                for x in xs {
                    self.resolve_refs(x)?;
                }
            }
            Node::Group { body, .. }
            | Node::NonCapGroup(body)
            | Node::ModGroup { body, .. }
            | Node::Quant { body, .. }
            | Node::Look { body, .. } => self.resolve_refs(body)?,
            _ => {}
        }
        Ok(())
    }
}

enum CAtom {
    Ch(u32),
    Esc(EscClass),
}

enum VElement {
    Op(VOperand),
    Range(u32, u32),
}

impl VElement {
    fn into_operand(self) -> VOperand {
        match self {
            VElement::Op(op) => op,
            VElement::Range(a, b) => VOperand::Range(a, b),
        }
    }
}

fn hex_val(c: u32) -> Option<u32> {
    match c {
        0x30..=0x39 => Some(c - 0x30),
        0x41..=0x46 => Some(c - 0x41 + 10),
        0x61..=0x66 => Some(c - 0x61 + 10),
        _ => None,
    }
}
