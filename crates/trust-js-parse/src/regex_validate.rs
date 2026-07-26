// trust-js-parse: syntactic validation of regular expression literals.
//
// Flags are validated exactly (duplicate/unknown flags, u+v exclusion). The
// pattern body is validated against the *main-spec* Pattern grammar with a
// three-way outcome: definitely valid → Ok; definitely invalid under every
// grammar (incl. Annex B) → Early; any construct whose validity differs
// between the main grammar and Annex B in non-unicode mode, or a surface we
// do not confidently model (unknown \p{...} names, v-mode class set
// operations, \q{...} string literals), is a sound Unsupported refusal —
// never a guessed verdict.
//
// Implemented per spec: quantifier placement/ranges, groups + named groups
// (with unicode escapes in names and the ES2025 duplicate-name rule: same
// name legal only across different alternatives), lookaround, inline
// modifier groups (?ims-ims: ), backreference bounds, \p{...}/\P{...} via
// generated UCD tables (unicode_props.rs), u-mode identity-escape
// restrictions, class ranges, and a conservative v-mode class subset.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::lexer::{is_id_continue, is_id_start, Fail};
use crate::unicode_props::{P_KNOWN_INVALID, P_VALID_U, P_VALID_V_ONLY};

pub fn validate_regex(pattern: &str, flags: &str) -> Result<(), Fail> {
    let mut seen = Vec::new();
    for c in flags.chars() {
        if !matches!(c, 'd' | 'g' | 'i' | 'm' | 's' | 'u' | 'v' | 'y') {
            return Err(Fail::early(format!("unknown regex flag '{c}'")));
        }
        if seen.contains(&c) {
            return Err(Fail::early(format!("duplicate regex flag '{c}'")));
        }
        seen.push(c);
    }
    if seen.contains(&'u') && seen.contains(&'v') {
        return Err(Fail::early("regex flags 'u' and 'v' are mutually exclusive"));
    }
    let unicode = seen.contains(&'u') || seen.contains(&'v');
    let vmode = seen.contains(&'v');
    let mut p = PatParser {
        chars: pattern.chars().collect(),
        pos: 0,
        unicode,
        vmode,
        ngroups: 0,
        names: Vec::new(),
        max_backref: 0,
        backref_names: Vec::new(),
        in_negated_class: false,
    };
    p.count_groups();
    p.disjunction(0)?;
    if p.pos != p.chars.len() {
        if p.peek() == Some(')') {
            return Err(Fail::early("unmatched ')' in regex"));
        }
        return Err(Fail::early("trailing garbage in regex pattern"));
    }
    if p.max_backref > p.ngroups {
        if p.unicode {
            return Err(Fail::early("regex backreference exceeds group count"));
        }
        // Annex B reinterprets such escapes; out of slice.
        return Err(Fail::unsupported(
            "regex: decimal escape exceeding group count (annexB divergent)",
        ));
    }
    for n in &p.backref_names {
        if !p.names.contains(n) {
            if p.names.is_empty() && !p.unicode {
                return Err(Fail::unsupported(
                    "regex: \\k escape without named groups (annexB divergent)",
                ));
            }
            return Err(Fail::early("regex \\k references unknown group name"));
        }
    }
    Ok(())
}

struct PatParser {
    chars: Vec<char>,
    pos: usize,
    unicode: bool,
    vmode: bool,
    ngroups: u32,
    names: Vec<String>,
    max_backref: u32,
    backref_names: Vec<String>,
    in_negated_class: bool,
}

impl PatParser {
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

    /// Pre-scan: count capturing groups and collect group names (backrefs
    /// may appear before their group). Name conflicts are validated by the
    /// recursive parse, not here.
    fn count_groups(&mut self) {
        let mut i = 0;
        let mut in_class = false;
        while i < self.chars.len() {
            let c = self.chars[i];
            match c {
                '\\' => i += 1,
                '[' if !in_class => in_class = true,
                ']' if in_class => in_class = false,
                '(' if !in_class => {
                    if self.chars.get(i + 1) == Some(&'?') {
                        if self.chars.get(i + 2) == Some(&'<')
                            && !matches!(self.chars.get(i + 3), Some('=') | Some('!'))
                        {
                            self.ngroups += 1;
                            let mut name = String::new();
                            let mut j = i + 3;
                            while j < self.chars.len() && self.chars[j] != '>' {
                                name.push(self.chars[j]);
                                j += 1;
                            }
                            if let Ok(cooked) = uncook_group_name(&name) {
                                self.names.push(cooked);
                            }
                        }
                    } else {
                        self.ngroups += 1;
                    }
                }
                _ => {}
            }
            i += 1;
        }
    }

    /// Returns the (deduplicated) set of group names declared in the
    /// subtree, for the same-alternative duplicate-name rule.
    fn disjunction(&mut self, depth: u32) -> Result<Vec<String>, Fail> {
        if depth > 100 {
            return Err(Fail::unsupported("regex nesting too deep"));
        }
        let mut all: Vec<String> = Vec::new();
        loop {
            let alt = self.alternative(depth)?;
            for n in alt {
                if !all.contains(&n) {
                    all.push(n);
                }
            }
            if self.peek() == Some('|') {
                self.pos += 1;
            } else {
                return Ok(all);
            }
        }
    }

    fn alternative(&mut self, depth: u32) -> Result<Vec<String>, Fail> {
        let mut names: Vec<String> = Vec::new();
        loop {
            match self.peek() {
                None | Some('|') | Some(')') => return Ok(names),
                _ => {
                    let sub = self.term(depth)?;
                    for n in sub {
                        if names.contains(&n) {
                            return Err(Fail::early(format!(
                                "duplicate capture group name '{n}' in the same alternative"
                            )));
                        }
                        names.push(n);
                    }
                }
            }
        }
    }

    fn term(&mut self, depth: u32) -> Result<Vec<String>, Fail> {
        let c = self.peek().unwrap();
        match c {
            '^' | '$' => {
                self.pos += 1;
                if self.at_quantifier() {
                    return Err(Fail::early("quantified anchor in regex"));
                }
                Ok(Vec::new())
            }
            '\\' if matches!(self.peek_at(1), Some('b') | Some('B')) => {
                self.pos += 2;
                if self.at_quantifier() {
                    return Err(Fail::early("quantified word-boundary assertion in regex"));
                }
                Ok(Vec::new())
            }
            '(' if self.peek_at(1) == Some('?')
                && (self.peek_at(2) == Some('=')
                    || self.peek_at(2) == Some('!')
                    || (self.peek_at(2) == Some('<')
                        && matches!(self.peek_at(3), Some('=') | Some('!')))) =>
            {
                let lookbehind = self.peek_at(2) == Some('<');
                self.pos += if lookbehind { 4 } else { 3 };
                let names = self.disjunction(depth + 1)?;
                if self.bump() != Some(')') {
                    return Err(Fail::early("unterminated regex group"));
                }
                if self.at_quantifier() {
                    if lookbehind {
                        return Err(Fail::early("quantified lookbehind in regex"));
                    }
                    if self.unicode {
                        return Err(Fail::early("quantified lookahead in u-mode regex"));
                    }
                    // Annex B allows quantified lookahead in non-u mode.
                    self.quantifier()?;
                }
                Ok(names)
            }
            '*' | '+' | '?' => Err(Fail::early("regex quantifier with nothing to repeat")),
            '{' => {
                if self.looks_like_braced_quantifier() {
                    Err(Fail::early("regex quantifier with nothing to repeat"))
                } else if self.unicode {
                    Err(Fail::early("lone '{' in unicode-mode regex"))
                } else {
                    Err(Fail::unsupported(
                        "regex: literal '{' (annexB ExtendedPatternCharacter)",
                    ))
                }
            }
            _ => {
                let names = self.atom(depth)?;
                if self.at_quantifier() {
                    self.quantifier()?;
                }
                Ok(names)
            }
        }
    }

    fn at_quantifier(&self) -> bool {
        match self.peek() {
            Some('*') | Some('+') | Some('?') => true,
            Some('{') => self.looks_like_braced_quantifier(),
            _ => false,
        }
    }

    fn looks_like_braced_quantifier(&self) -> bool {
        let mut i = self.pos + 1;
        let mut any = false;
        while matches!(self.chars.get(i), Some(c) if c.is_ascii_digit()) {
            any = true;
            i += 1;
        }
        if !any {
            return false;
        }
        if self.chars.get(i) == Some(&',') {
            i += 1;
            while matches!(self.chars.get(i), Some(c) if c.is_ascii_digit()) {
                i += 1;
            }
        }
        self.chars.get(i) == Some(&'}')
    }

    fn quantifier(&mut self) -> Result<(), Fail> {
        match self.peek() {
            Some('*') | Some('+') | Some('?') => {
                self.pos += 1;
            }
            Some('{') => {
                self.pos += 1;
                let lo = self.digits();
                let mut hi = lo;
                if self.peek() == Some(',') {
                    self.pos += 1;
                    if self.peek() != Some('}') {
                        hi = self.digits();
                    } else {
                        hi = u64::MAX;
                    }
                }
                if self.bump() != Some('}') {
                    return Err(Fail::early("malformed braced quantifier"));
                }
                if lo > hi {
                    return Err(Fail::early("regex quantifier range out of order"));
                }
            }
            _ => unreachable!(),
        }
        if self.peek() == Some('?') {
            self.pos += 1; // non-greedy
        }
        if self.at_quantifier() {
            return Err(Fail::early("regex quantifier with nothing to repeat"));
        }
        Ok(())
    }

    fn digits(&mut self) -> u64 {
        let mut v: u64 = 0;
        while let Some(d) = self.peek().and_then(|c| c.to_digit(10)) {
            v = v.saturating_mul(10).saturating_add(d as u64);
            self.pos += 1;
        }
        v
    }

    fn atom(&mut self, depth: u32) -> Result<Vec<String>, Fail> {
        match self.peek().unwrap() {
            '.' => {
                self.pos += 1;
                Ok(Vec::new())
            }
            '(' => {
                self.pos += 1;
                let mut own_name = None;
                if self.peek() == Some('?') {
                    self.pos += 1;
                    match self.peek() {
                        Some(':') => {
                            self.pos += 1;
                        }
                        Some('<') => {
                            self.pos += 1;
                            let name = self.group_name()?;
                            own_name = Some(name);
                        }
                        Some('i') | Some('m') | Some('s') | Some('-') => {
                            self.modifier_flags()?;
                        }
                        _ => return Err(Fail::early("malformed regex group")),
                    }
                }
                let mut names = self.disjunction(depth + 1)?;
                if self.bump() != Some(')') {
                    return Err(Fail::early("unterminated regex group"));
                }
                if let Some(n) = own_name {
                    if names.contains(&n) {
                        return Err(Fail::early(format!(
                            "duplicate capture group name '{n}' in the same alternative"
                        )));
                    }
                    names.push(n);
                }
                Ok(names)
            }
            ')' => Err(Fail::early("unmatched ')' in regex")),
            '[' => {
                if self.vmode {
                    self.char_class_v()?;
                } else {
                    self.char_class()?;
                }
                Ok(Vec::new())
            }
            ']' => {
                if self.unicode {
                    Err(Fail::early("lone ']' in unicode-mode regex"))
                } else {
                    Err(Fail::unsupported(
                        "regex: literal ']' (annexB ExtendedPatternCharacter)",
                    ))
                }
            }
            '}' => {
                if self.unicode {
                    Err(Fail::early("lone '}' in unicode-mode regex"))
                } else {
                    Err(Fail::unsupported(
                        "regex: literal '}' (annexB ExtendedPatternCharacter)",
                    ))
                }
            }
            '\\' => {
                self.pos += 1;
                self.atom_escape()?;
                Ok(Vec::new())
            }
            _ => {
                self.pos += 1;
                Ok(Vec::new())
            }
        }
    }

    /// Inline modifier flags `(?ims-ims:` — RegExp pattern modifiers.
    fn modifier_flags(&mut self) -> Result<(), Fail> {
        let mut add = Vec::new();
        let mut remove = Vec::new();
        let mut in_remove = false;
        loop {
            match self.peek() {
                Some(':') => {
                    self.pos += 1;
                    break;
                }
                Some('-') if !in_remove => {
                    in_remove = true;
                    self.pos += 1;
                }
                Some(c) if matches!(c, 'i' | 'm' | 's') => {
                    let set = if in_remove { &mut remove } else { &mut add };
                    if set.contains(&c) {
                        return Err(Fail::early("duplicate flag in regex modifier group"));
                    }
                    set.push(c);
                    self.pos += 1;
                }
                _ => return Err(Fail::early("malformed regex modifier group")),
            }
        }
        if add.is_empty() && remove.is_empty() {
            return Err(Fail::early("empty regex modifier group"));
        }
        if in_remove && remove.is_empty() && add.is_empty() {
            return Err(Fail::early("empty regex modifier group"));
        }
        for c in &add {
            if remove.contains(c) {
                return Err(Fail::early(
                    "flag both added and removed in regex modifier group",
                ));
            }
        }
        Ok(())
    }

    /// RegExpIdentifierName up to `>`, with \u escapes cooked and validated.
    fn group_name(&mut self) -> Result<String, Fail> {
        let mut raw = String::new();
        loop {
            match self.peek() {
                Some('>') => {
                    self.pos += 1;
                    break;
                }
                Some(c) => {
                    raw.push(c);
                    self.pos += 1;
                }
                None => return Err(Fail::early("malformed regex group name")),
            }
        }
        let name = uncook_group_name(&raw)
            .map_err(|_| Fail::early("malformed unicode escape in regex group name"))?;
        let mut chars = name.chars();
        match chars.next() {
            Some(c) if is_id_start(c) => {}
            _ => return Err(Fail::early("invalid regex group name")),
        }
        for c in chars {
            if !is_id_continue(c) {
                return Err(Fail::early("invalid regex group name"));
            }
        }
        Ok(name)
    }

    /// `\p{...}` / `\P{...}` — table-driven validation. `negated` covers
    /// both `\P` and containment in a negated (`[^…]`) v-mode class, where
    /// properties of strings are invalid.
    fn property_escape(&mut self, negated: bool) -> Result<(), Fail> {
        // At the char after 'p'/'P'.
        if self.peek() != Some('{') {
            return Err(Fail::early("malformed \\p escape in unicode-mode regex"));
        }
        self.pos += 1;
        let mut name = String::new();
        loop {
            match self.peek() {
                Some('}') => {
                    self.pos += 1;
                    break;
                }
                Some(c) => {
                    name.push(c);
                    self.pos += 1;
                }
                None => return Err(Fail::early("unterminated \\p{...} in regex")),
            }
        }
        if name.is_empty() {
            return Err(Fail::early("empty \\p{} property name in regex"));
        }
        if P_VALID_U.binary_search(&name.as_str()).is_ok() {
            return Ok(());
        }
        if P_VALID_V_ONLY.binary_search(&name.as_str()).is_ok() {
            // Properties of strings: valid only in v-mode and never negated.
            if self.vmode && !negated {
                return Ok(());
            }
            return Err(Fail::early(
                "string property escape invalid here (negated or non-v mode)",
            ));
        }
        if P_KNOWN_INVALID.binary_search(&name.as_str()).is_ok() {
            return Err(Fail::early(format!(
                "unknown unicode property '{name}' in regex"
            )));
        }
        Err(Fail::unsupported(format!(
            "regex: unicode property '{name}' not in the modeled table"
        )))
    }

    fn atom_escape(&mut self) -> Result<(), Fail> {
        let c = match self.peek() {
            None => return Err(Fail::early("trailing backslash in regex")),
            Some(c) => c,
        };
        match c {
            'd' | 'D' | 's' | 'S' | 'w' | 'W' => {
                self.pos += 1;
                Ok(())
            }
            'p' | 'P' => {
                if self.unicode {
                    self.pos += 1;
                    self.property_escape(c == 'P')
                } else {
                    Err(Fail::unsupported("regex: \\p in non-unicode mode (annexB)"))
                }
            }
            'k' => {
                self.pos += 1;
                if self.peek() == Some('<') {
                    self.pos += 1;
                    let name = self.group_name()?;
                    self.backref_names.push(name);
                    Ok(())
                } else if self.unicode {
                    Err(Fail::early("malformed \\k escape in regex"))
                } else {
                    Err(Fail::unsupported("regex: \\k identity escape (annexB)"))
                }
            }
            '1'..='9' => {
                let n = self.digits();
                self.max_backref = self.max_backref.max(n.min(u32::MAX as u64) as u32);
                Ok(())
            }
            '0' => {
                self.pos += 1;
                if self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    if self.unicode {
                        return Err(Fail::early("\\0 followed by digit in u-mode regex"));
                    }
                    return Err(Fail::unsupported("regex: legacy octal escape (annexB)"));
                }
                Ok(())
            }
            'f' | 'n' | 'r' | 't' | 'v' => {
                self.pos += 1;
                Ok(())
            }
            'c' => {
                self.pos += 1;
                if self.peek().is_some_and(|c| c.is_ascii_alphabetic()) {
                    self.pos += 1;
                    Ok(())
                } else if self.unicode {
                    Err(Fail::early("malformed \\c escape in u-mode regex"))
                } else {
                    Err(Fail::unsupported("regex: bare \\c (annexB)"))
                }
            }
            'x' => {
                self.pos += 1;
                if self.peek().is_some_and(|c| c.is_ascii_hexdigit())
                    && self.peek_at(1).is_some_and(|c| c.is_ascii_hexdigit())
                {
                    self.pos += 2;
                    Ok(())
                } else if self.unicode {
                    Err(Fail::early("malformed \\x escape in u-mode regex"))
                } else {
                    Err(Fail::unsupported("regex: bare \\x identity (annexB)"))
                }
            }
            'u' => {
                self.pos += 1;
                self.unicode_escape()?;
                Ok(())
            }
            _ => self.identity_escape(c),
        }
    }

    fn identity_escape(&mut self, c: char) -> Result<(), Fail> {
        let syntax = matches!(
            c,
            '^' | '$' | '\\' | '.' | '*' | '+' | '?' | '(' | ')' | '[' | ']' | '{' | '}' | '|'
                | '/'
        );
        if syntax {
            self.pos += 1;
            return Ok(());
        }
        if self.vmode
            && matches!(
                c,
                '!' | '#' | '%' | '&' | ',' | '-' | ':' | ';' | '<' | '=' | '>' | '@' | '`'
                    | '~' | '"' | '\''
            )
        {
            self.pos += 1;
            return Ok(());
        }
        if self.unicode {
            return Err(Fail::early(format!(
                "invalid identity escape '\\{c}' in unicode-mode regex"
            )));
        }
        // Main-spec non-unicode IdentityEscape: SourceCharacter but not
        // UnicodeIDContinue. Annex B widens further (letters/digits get
        // special meanings) — those go through the named cases above or are
        // refused here.
        if !is_id_continue(c) {
            self.pos += 1;
            return Ok(());
        }
        Err(Fail::unsupported(format!(
            "regex: identity escape '\\{c}' of ID_Continue char (annexB divergent)"
        )))
    }

    fn unicode_escape(&mut self) -> Result<(), Fail> {
        // After \u.
        if self.peek() == Some('{') {
            if !self.unicode {
                return Err(Fail::unsupported(
                    "regex: \\u{...} in non-unicode mode (annexB identity)",
                ));
            }
            self.pos += 1;
            let mut v: u32 = 0;
            let mut any = false;
            while let Some(d) = self.peek().and_then(|c| c.to_digit(16)) {
                any = true;
                v = v.saturating_mul(16).saturating_add(d);
                self.pos += 1;
            }
            if !any || self.peek() != Some('}') {
                return Err(Fail::early("malformed \\u{...} in regex"));
            }
            if v > 0x10FFFF {
                return Err(Fail::early("regex \\u{...} out of range"));
            }
            self.pos += 1;
            Ok(())
        } else {
            for _ in 0..4 {
                if !self.peek().is_some_and(|c| c.is_ascii_hexdigit()) {
                    if self.unicode {
                        return Err(Fail::early("malformed \\u escape in u-mode regex"));
                    }
                    return Err(Fail::unsupported("regex: bare \\u identity (annexB)"));
                }
                self.pos += 1;
            }
            Ok(())
        }
    }

    fn char_class(&mut self) -> Result<(), Fail> {
        // At '[' (u-mode or legacy mode).
        self.pos += 1;
        if self.peek() == Some('^') {
            self.pos += 1;
        }
        let mut prev: Option<ClassAtom> = None;
        let mut pending_range = false;
        loop {
            match self.peek() {
                None => return Err(Fail::early("unterminated regex character class")),
                Some(']') => {
                    self.pos += 1;
                    return Ok(());
                }
                Some('-') if prev.is_some() && !pending_range && self.peek_at(1) != Some(']') => {
                    self.pos += 1;
                    pending_range = true;
                }
                _ => {
                    let atom = self.class_atom()?;
                    if pending_range {
                        let lo = prev.take().unwrap();
                        match (&lo, &atom) {
                            (ClassAtom::Char(a), ClassAtom::Char(b)) => {
                                if a > b {
                                    return Err(Fail::early("regex class range out of order"));
                                }
                            }
                            _ => {
                                if self.unicode {
                                    return Err(Fail::early(
                                        "class escape in range bound (u-mode regex)",
                                    ));
                                }
                                return Err(Fail::unsupported(
                                    "regex: class-escape range bound (annexB)",
                                ));
                            }
                        }
                        pending_range = false;
                        prev = None;
                    } else {
                        prev = Some(atom);
                    }
                }
            }
        }
    }

    /// v-mode class: ClassSetExpression — union with ranges, intersection
    /// (`&&`), subtraction (`--`), nested classes, `\q{...}` string
    /// disjunctions, with the reserved/doubled-punctuator rules and the
    /// no-strings-in-negated-class rule.
    fn char_class_v(&mut self) -> Result<(), Fail> {
        self.pos += 1; // [
        let negated = self.peek() == Some('^');
        if negated {
            self.pos += 1;
        }
        let saved_neg = self.in_negated_class;
        // MayContainStrings propagates: strings are illegal anywhere under a
        // negated class.
        self.in_negated_class = saved_neg || negated;
        let r = self.char_class_v_body();
        self.in_negated_class = saved_neg;
        r
    }

    fn v_reserved_punct(c: char) -> bool {
        matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | '/' | '-' | '\\' | '|')
    }

    fn v_double_punct(c: char) -> bool {
        matches!(
            c,
            '&' | '!' | '#' | '$' | '%' | '*' | '+' | ',' | '.' | ':' | ';' | '<' | '=' | '>'
                | '?' | '@' | '^' | '`' | '~'
        )
    }

    /// One ClassSetOperand (no ranges). Returns the atom.
    fn v_operand(&mut self) -> Result<ClassAtom, Fail> {
        match self.peek() {
            None => Err(Fail::early("unterminated regex character class")),
            Some('[') => {
                self.char_class_v()?;
                Ok(ClassAtom::Escape)
            }
            Some('\\') if self.peek_at(1) == Some('q') => {
                self.v_string_disjunction()?;
                Ok(ClassAtom::Escape)
            }
            Some('\\') => self.class_atom(),
            Some(c) if Self::v_reserved_punct(c) => Err(Fail::early(
                "reserved punctuator must be escaped in v-mode class",
            )),
            Some(c) if Self::v_double_punct(c) && self.peek_at(1) == Some(c) => {
                Err(Fail::early("doubled punctuator in v-mode class"))
            }
            Some(c) => {
                self.pos += 1;
                Ok(ClassAtom::Char(c as u32))
            }
        }
    }

    /// `\q{ ClassString (| ClassString)* }`.
    fn v_string_disjunction(&mut self) -> Result<(), Fail> {
        self.pos += 2; // \q
        if self.peek() != Some('{') {
            return Err(Fail::early("malformed \\q in v-mode class"));
        }
        self.pos += 1;
        let mut cur_len: u32 = 0;
        loop {
            match self.peek() {
                None => return Err(Fail::early("unterminated \\q{...} in v-mode class")),
                Some('}') => {
                    self.pos += 1;
                    if cur_len != 1 && self.in_negated_class {
                        return Err(Fail::early(
                            "string disjunction in negated v-mode class",
                        ));
                    }
                    return Ok(());
                }
                Some('|') => {
                    if cur_len != 1 && self.in_negated_class {
                        return Err(Fail::early(
                            "string disjunction in negated v-mode class",
                        ));
                    }
                    cur_len = 0;
                    self.pos += 1;
                }
                Some('\\') => {
                    // Character escapes are fine inside strings; class
                    // escapes (\d, \p{...}, …) are not.
                    if matches!(
                        self.peek_at(1),
                        Some('d') | Some('D') | Some('s') | Some('S') | Some('w') | Some('W')
                            | Some('p') | Some('P')
                    ) {
                        return Err(Fail::early(
                            "class escape inside \\q string in v-mode class",
                        ));
                    }
                    let _ = self.class_atom()?;
                    cur_len += 1;
                }
                Some(c) if Self::v_reserved_punct(c) => {
                    return Err(Fail::early(
                        "reserved punctuator must be escaped in v-mode class",
                    ))
                }
                Some(_) => {
                    self.pos += 1;
                    cur_len += 1;
                }
            }
        }
    }

    fn char_class_v_body(&mut self) -> Result<(), Fail> {
        if self.peek() == Some(']') {
            self.pos += 1; // empty class
            return Ok(());
        }
        // First element (operand or range).
        let mut count = 0usize;
        let mut mode: Option<&'static str> = None; // "&&" | "--" | "union"
        loop {
            match self.peek() {
                None => return Err(Fail::early("unterminated regex character class")),
                Some(']') => {
                    self.pos += 1;
                    return Ok(());
                }
                Some('&') if self.peek_at(1) == Some('&') => {
                    if self.peek_at(2) == Some('&') {
                        return Err(Fail::early("'&&&' in v-mode class"));
                    }
                    match mode {
                        None if count == 1 => mode = Some("&&"),
                        Some("&&") => {}
                        _ => {
                            return Err(Fail::early(
                                "mixed set operators in v-mode class",
                            ))
                        }
                    }
                    self.pos += 2;
                    let _ = self.v_operand()?;
                    count += 1;
                }
                Some('-') if self.peek_at(1) == Some('-') => {
                    match mode {
                        None if count == 1 => mode = Some("--"),
                        Some("--") => {}
                        _ => {
                            return Err(Fail::early(
                                "mixed set operators in v-mode class",
                            ))
                        }
                    }
                    self.pos += 2;
                    let _ = self.v_operand()?;
                    count += 1;
                }
                _ => {
                    if mode.is_some() && mode != Some("union") {
                        return Err(Fail::early("mixed set operators in v-mode class"));
                    }
                    if count > 0 {
                        mode = Some("union");
                    }
                    let atom = self.v_operand()?;
                    count += 1;
                    // Range?
                    if self.peek() == Some('-')
                        && self.peek_at(1) != Some('-')
                        && self.peek_at(1) != Some(']')
                        && self.peek_at(1).is_some()
                    {
                        if mode == Some("&&") || mode == Some("--") {
                            return Err(Fail::early("mixed set operators in v-mode class"));
                        }
                        mode = Some("union");
                        self.pos += 1; // -
                        let hi = self.v_operand()?;
                        count += 1;
                        match (&atom, &hi) {
                            (ClassAtom::Char(a), ClassAtom::Char(b)) => {
                                if a > b {
                                    return Err(Fail::early(
                                        "regex class range out of order",
                                    ));
                                }
                            }
                            _ => {
                                return Err(Fail::early(
                                    "non-character range bound in v-mode class",
                                ))
                            }
                        }
                    }
                }
            }
        }
    }

    fn class_atom(&mut self) -> Result<ClassAtom, Fail> {
        let c = self.peek().unwrap();
        if c != '\\' {
            self.pos += 1;
            return Ok(ClassAtom::Char(c as u32));
        }
        self.pos += 1;
        let e = match self.peek() {
            None => return Err(Fail::early("trailing backslash in regex class")),
            Some(e) => e,
        };
        match e {
            'd' | 'D' | 's' | 'S' | 'w' | 'W' => {
                self.pos += 1;
                Ok(ClassAtom::Escape)
            }
            'p' | 'P' => {
                if self.unicode {
                    self.pos += 1;
                    let neg = e == 'P' || self.in_negated_class;
                    self.property_escape(neg)?;
                    Ok(ClassAtom::Escape)
                } else {
                    Err(Fail::unsupported("regex: \\p in non-unicode class (annexB)"))
                }
            }
            'b' => {
                self.pos += 1;
                Ok(ClassAtom::Char(0x8))
            }
            '-' => {
                self.pos += 1;
                Ok(ClassAtom::Char('-' as u32))
            }
            'f' => {
                self.pos += 1;
                Ok(ClassAtom::Char(0xC))
            }
            'n' => {
                self.pos += 1;
                Ok(ClassAtom::Char(0xA))
            }
            'r' => {
                self.pos += 1;
                Ok(ClassAtom::Char(0xD))
            }
            't' => {
                self.pos += 1;
                Ok(ClassAtom::Char(0x9))
            }
            'v' => {
                self.pos += 1;
                Ok(ClassAtom::Char(0xB))
            }
            'c' => {
                self.pos += 1;
                if self.peek().is_some_and(|c| c.is_ascii_alphabetic()) {
                    let l = self.bump().unwrap();
                    Ok(ClassAtom::Char((l as u32) % 32))
                } else if self.unicode {
                    Err(Fail::early("malformed \\c in u-mode regex class"))
                } else {
                    Err(Fail::unsupported("regex: bare \\c in class (annexB)"))
                }
            }
            'x' => {
                self.pos += 1;
                if self.peek().is_some_and(|c| c.is_ascii_hexdigit())
                    && self.peek_at(1).is_some_and(|c| c.is_ascii_hexdigit())
                {
                    let v = self.peek().unwrap().to_digit(16).unwrap() * 16
                        + self.peek_at(1).unwrap().to_digit(16).unwrap();
                    self.pos += 2;
                    Ok(ClassAtom::Char(v))
                } else if self.unicode {
                    Err(Fail::early("malformed \\x in u-mode regex class"))
                } else {
                    Err(Fail::unsupported("regex: bare \\x in class (annexB)"))
                }
            }
            'u' => {
                self.pos += 1;
                self.unicode_escape()?;
                // Range-bound value tracking over \u escapes is not modeled.
                Ok(ClassAtom::Escape)
            }
            '0' => {
                self.pos += 1;
                if self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    if self.unicode {
                        return Err(Fail::early("octal escape in u-mode regex class"));
                    }
                    return Err(Fail::unsupported("regex: octal escape in class (annexB)"));
                }
                Ok(ClassAtom::Char(0))
            }
            '1'..='9' => {
                if self.unicode {
                    Err(Fail::early("decimal escape in u-mode regex class"))
                } else {
                    Err(Fail::unsupported("regex: decimal escape in class (annexB)"))
                }
            }
            _ => {
                let syntax = matches!(
                    e,
                    '^' | '$' | '\\' | '.' | '*' | '+' | '?' | '(' | ')' | '[' | ']' | '{' | '}'
                        | '|' | '/'
                );
                if syntax {
                    self.pos += 1;
                    return Ok(ClassAtom::Char(e as u32));
                }
                if self.vmode
                    && matches!(
                        e,
                        '!' | '#' | '%' | '&' | ',' | '-' | ':' | ';' | '<' | '=' | '>' | '@'
                            | '`' | '~' | '"' | '\''
                    )
                {
                    self.pos += 1;
                    return Ok(ClassAtom::Char(e as u32));
                }
                if self.unicode {
                    return Err(Fail::early(format!(
                        "invalid identity escape '\\{e}' in unicode-mode regex class"
                    )));
                }
                if !is_id_continue(e) {
                    self.pos += 1;
                    return Ok(ClassAtom::Char(e as u32));
                }
                Err(Fail::unsupported(format!(
                    "regex: identity escape '\\{e}' of ID_Continue char in class (annexB)"
                )))
            }
        }
    }
}

enum ClassAtom {
    Char(u32),
    Escape,
}

/// Cook \u escapes in a raw group name.
fn uncook_group_name(raw: &str) -> Result<String, ()> {
    if raw.is_empty() {
        return Err(());
    }
    let chars: Vec<char> = raw.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] != '\\' {
            out.push(chars[i]);
            i += 1;
            continue;
        }
        if chars.get(i + 1) != Some(&'u') {
            return Err(());
        }
        i += 2;
        if chars.get(i) == Some(&'{') {
            i += 1;
            let mut v: u32 = 0;
            let mut any = false;
            while i < chars.len() && chars[i] != '}' {
                match chars[i].to_digit(16) {
                    Some(d) => {
                        any = true;
                        v = v.saturating_mul(16).saturating_add(d);
                    }
                    None => return Err(()),
                }
                i += 1;
            }
            if !any || i >= chars.len() || v > 0x10FFFF {
                return Err(());
            }
            i += 1; // }
            out.push(char::from_u32(v).ok_or(())?);
        } else {
            if i + 4 > chars.len() {
                return Err(());
            }
            let mut v: u32 = 0;
            for k in 0..4 {
                v = v * 16 + chars[i + k].to_digit(16).ok_or(())?;
            }
            i += 4;
            // Surrogate pair: \uD800-\uDBFF followed by \uDC00-\uDFFF.
            if (0xD800..=0xDBFF).contains(&v)
                && chars.get(i) == Some(&'\\')
                && chars.get(i + 1) == Some(&'u')
                && i + 6 <= chars.len()
            {
                let mut lo: u32 = 0;
                let mut ok = true;
                for k in 0..4 {
                    match chars[i + 2 + k].to_digit(16) {
                        Some(d) => lo = lo * 16 + d,
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok && (0xDC00..=0xDFFF).contains(&lo) {
                    i += 6;
                    let cp = 0x10000 + ((v - 0xD800) << 10) + (lo - 0xDC00);
                    out.push(char::from_u32(cp).ok_or(())?);
                    continue;
                }
            }
            out.push(char::from_u32(v).ok_or(())?);
        }
    }
    if out.is_empty() {
        return Err(());
    }
    Ok(out)
}
