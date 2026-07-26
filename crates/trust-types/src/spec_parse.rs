// trust-types/spec_parse.rs: Parser for simple contract expressions
//
// Parses spec expression strings from #[requires("...")], #[ensures("...")], etc.
// into Formula values suitable for SMT solving.
//
// Supports:
// - Boolean operators: &&, ||, !, =>
// - Comparison operators: <, <=, >, >=, ==, !=
// - Arithmetic: +, -, *, /
// - Native quantifiers: forall i j: usize, expr; exists x: T, expr
// - Attribute-compat quantifiers: forall(i, 0..n, expr), exists(i, 0..n, expr)
// - Method-style access: arr.len(), s.is_empty()
// - Native result name: result (maps to _0)
// - Attribute compatibility only: old(x) (maps to old_x)
//
// Primed post-state names are rejected until the typed frontend supplies an
// exact MIR-place/state binding. Accepting them here would create free terms.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::spec::SpecParseError;
use crate::{Formula, Sort, is_valid_pred, pred_arg_sorts};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Token {
    Ident(String),
    Int(i128),
    /// An IEEE-754 binary64 literal, stored as its raw bits so the `Token` enum
    /// keeps `Eq` (f64 is not `Eq`). Produced for `1.0e30` / `1e30` /
    /// `1000000000000000000000000000000.0` and lowered to `Formula::FpConst`.
    Float(u64),
    Gt,
    Ge,
    Lt,
    Le,
    EqEq,
    Ne,
    Plus,
    Minus,
    Star,
    Slash,
    AndAnd,
    OrOr,
    Bang,
    Implies,
    LParen,
    RParen,
    Comma,
    Dot,
    DotDot,
    Colon,
    Percent,
    LBracket,
    RBracket,
}

/// Parse a simple specification predicate body into a solver formula.
///
/// Returns `None` on any parse failure. For structured errors, use
/// [`parse_spec_expr_result`] instead.
#[must_use]
pub fn parse_spec_expr(input: &str) -> Option<Formula> {
    parse_spec_expr_result(input).ok()
}

/// Parse a specification expression with structured error reporting.
pub fn parse_spec_expr_result(input: &str) -> Result<Formula, SpecParseError> {
    if input.trim().is_empty() {
        return Err(SpecParseError::Empty);
    }

    let tokens = tokenize(input)?;
    let mut parser = Parser::new(tokens);
    let formula = parser.parse_implies()?;

    if parser.is_eof() { Ok(formula) } else { Err(SpecParseError::TrailingTokens) }
}

pub(crate) fn tokenize(input: &str) -> Result<Vec<Token>, SpecParseError> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0;

    while index < bytes.len() {
        let byte = bytes[index];

        if byte.is_ascii_whitespace() {
            index += 1;
            continue;
        }

        if byte.is_ascii_digit() {
            let start = index;
            index += 1;

            while index < bytes.len() && bytes[index].is_ascii_digit() {
                index += 1;
            }

            // A digit-led token is an f64 LITERAL when it carries a fractional part
            // and/or a decimal exponent — the two markers a spec-language float bound
            // (`self.0 <= 1.0e30`) needs. Otherwise it stays an integer literal, so
            // plain integers, the `..` range token, and a tuple-field `.0` AFTER an
            // identifier (which lexes via the ident branch, never here) are unchanged.
            //
            // PROJECTION CONTEXT: a digit run whose PRECEDING token is `Dot` is a
            // tuple-field INDEX, never a float — `self.0.0` must lex as
            // [Ident, Dot, Int(0), Dot, Int(0)] (two nested field segments), not
            // [Ident, Dot, Float(0.0)]. No valid spec expression puts a float
            // literal directly after `.` (`Dot` is only projection; ranges are the
            // separate `DotDot` token), so suppressing float lexing here is exact.
            // Without it every CONSECUTIVE numeric field pair — `(*self).0.0`,
            // the canonicalized spelling of a nested-struct bound like
            // `self.min.x` — was unlexable and the whole contract died as
            // SpecUnverifiable (fail-closed but silently feature-dead).
            let field_index_context = matches!(tokens.last(), Some(Token::Dot));
            let mut is_float = false;
            // Fractional part: `.` IMMEDIATELY followed by a digit. Requiring the
            // trailing digit keeps `0..n` (the range `..`) an integer + `DotDot`, and
            // `1.method()` an integer + `Dot` + method.
            if !field_index_context
                && index + 1 < bytes.len()
                && bytes[index] == b'.'
                && bytes[index + 1].is_ascii_digit()
            {
                is_float = true;
                index += 1; // consume '.'
                while index < bytes.len() && bytes[index].is_ascii_digit() {
                    index += 1;
                }
            }
            // Exponent part: `e`/`E`, an optional sign, then at least one digit. Only
            // committed when a digit follows, so a bare trailing `e` is not consumed.
            if index < bytes.len() && (bytes[index] == b'e' || bytes[index] == b'E') {
                let mut look = index + 1;
                if look < bytes.len() && (bytes[look] == b'+' || bytes[look] == b'-') {
                    look += 1;
                }
                if look < bytes.len() && bytes[look].is_ascii_digit() {
                    is_float = true;
                    index = look + 1;
                    while index < bytes.len() && bytes[index].is_ascii_digit() {
                        index += 1;
                    }
                }
            }

            if is_float {
                let value = input[start..index].parse::<f64>().map_err(|_| {
                    SpecParseError::UnexpectedToken {
                        position: start,
                        expected: "valid floating-point literal".into(),
                    }
                })?;
                tokens.push(Token::Float(value.to_bits()));
                continue;
            }

            let value = input[start..index].parse::<i128>().map_err(|_| {
                SpecParseError::UnexpectedToken {
                    position: start,
                    expected: "valid integer literal".into(),
                }
            })?;
            tokens.push(Token::Int(value));
            continue;
        }

        if byte.is_ascii_alphabetic() || byte == b'_' {
            let start = index;
            index += 1;

            while index < bytes.len()
                && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
            {
                index += 1;
            }

            // A trailing prime is reserved for future post-state syntax. The
            // formula parser has no state environment, so accepting it as part
            // of a name would silently create an unconstrained free variable.
            if index < bytes.len() && bytes[index] == b'\'' {
                return Err(SpecParseError::UnexpectedChar { ch: '\'', position: index });
            }

            tokens.push(Token::Ident(input[start..index].to_string()));
            continue;
        }

        // First-class native clauses historically spell implication `==>`.
        // Recognize the contiguous three-byte token before the `==` arm so it
        // has the same verifier meaning as the compatibility spelling `=>`.
        if bytes.get(index..index.saturating_add(3)) == Some(b"==>".as_slice()) {
            index += 3;
            tokens.push(Token::Implies);
            continue;
        }

        let token = match (byte, bytes.get(index + 1).copied()) {
            (b'>', Some(b'=')) => {
                index += 2;
                Token::Ge
            }
            (b'<', Some(b'=')) => {
                index += 2;
                Token::Le
            }
            (b'=', Some(b'=')) => {
                index += 2;
                Token::EqEq
            }
            (b'!', Some(b'=')) => {
                index += 2;
                Token::Ne
            }
            (b'&', Some(b'&')) => {
                index += 2;
                Token::AndAnd
            }
            (b'|', Some(b'|')) => {
                index += 2;
                Token::OrOr
            }
            (b'=', Some(b'>')) => {
                index += 2;
                Token::Implies
            }
            (b'.', Some(b'.')) => {
                index += 2;
                Token::DotDot
            }
            (b'>', _) => {
                index += 1;
                Token::Gt
            }
            (b'<', _) => {
                index += 1;
                Token::Lt
            }
            (b'+', _) => {
                index += 1;
                Token::Plus
            }
            (b'-', _) => {
                index += 1;
                Token::Minus
            }
            (b'*', _) => {
                index += 1;
                Token::Star
            }
            (b'/', _) => {
                index += 1;
                Token::Slash
            }
            (b'!', _) => {
                index += 1;
                Token::Bang
            }
            (b'(', _) => {
                index += 1;
                Token::LParen
            }
            (b')', _) => {
                index += 1;
                Token::RParen
            }
            (b',', _) => {
                index += 1;
                Token::Comma
            }
            (b'.', _) => {
                index += 1;
                Token::Dot
            }
            (b':', _) => {
                index += 1;
                Token::Colon
            }
            (b'%', _) => {
                index += 1;
                Token::Percent
            }
            (b'[', _) => {
                index += 1;
                Token::LBracket
            }
            (b']', _) => {
                index += 1;
                Token::RBracket
            }
            _ => {
                return Err(SpecParseError::UnexpectedChar { ch: byte as char, position: index });
            }
        };

        tokens.push(token);
    }

    Ok(tokens)
}

/// Resolve a fixed-width primitive integer associated constant exactly.
///
/// Pointer-width constants are intentionally not accepted here: this parser is
/// also used outside a rustc target context, so guessing the host width for a
/// cross-target contract would be unsound. Producers that know the MIR integer
/// width must emit the corresponding numeric literal instead.
pub(crate) fn primitive_integer_constant(type_name: &str, constant: &str) -> Option<Formula> {
    let unsigned_width = match type_name {
        "u8" => Some(8),
        "u16" => Some(16),
        "u32" => Some(32),
        "u64" => Some(64),
        "u128" => Some(128),
        _ => None,
    };
    if let Some(width) = unsigned_width {
        return match constant {
            "MIN" => Some(Formula::Int(0)),
            "MAX" if width == 128 => Some(Formula::UInt(u128::MAX)),
            "MAX" => Some(Formula::Int(((1_u128 << width) - 1) as i128)),
            _ => None,
        };
    }

    let signed_width = match type_name {
        "i8" => Some(8),
        "i16" => Some(16),
        "i32" => Some(32),
        "i64" => Some(64),
        "i128" => Some(128),
        _ => None,
    };
    signed_width.and_then(|width| match constant {
        "MIN" if width == 128 => Some(Formula::Int(i128::MIN)),
        "MAX" if width == 128 => Some(Formula::Int(i128::MAX)),
        "MIN" => Some(Formula::Int(-(1_i128 << (width - 1)))),
        "MAX" => Some(Formula::Int((1_i128 << (width - 1)) - 1)),
        _ => None,
    })
}

struct Parser {
    tokens: Vec<Token>,
    index: usize,
    /// Lexically-scoped sorts for typed quantifier binders. Leaf variables
    /// otherwise default to `Int` and are retyped by later function context.
    bound_sorts: Vec<(String, Sort)>,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, index: 0, bound_sorts: Vec::new() }
    }

    fn is_eof(&self) -> bool {
        self.index == self.tokens.len()
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.index)
    }

    fn bump(&mut self) -> Result<Token, SpecParseError> {
        self.tokens
            .get(self.index)
            .cloned()
            .inspect(|_t| {
                self.index += 1;
            })
            .ok_or_else(|| SpecParseError::UnexpectedEof { expected: "token".into() })
    }

    fn eat(&mut self, expected: &Token) -> bool {
        if self.peek() == Some(expected) {
            self.index += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &Token, label: &str) -> Result<(), SpecParseError> {
        if self.eat(expected) {
            Ok(())
        } else if self.is_eof() {
            Err(SpecParseError::UnexpectedEof { expected: label.into() })
        } else {
            Err(SpecParseError::UnexpectedToken { position: self.index, expected: label.into() })
        }
    }

    fn parse_implies(&mut self) -> Result<Formula, SpecParseError> {
        let lhs = self.parse_or()?;

        if self.eat(&Token::Implies) {
            let rhs = self.parse_implies()?;
            Ok(Formula::Implies(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    fn parse_or(&mut self) -> Result<Formula, SpecParseError> {
        let first = self.parse_and()?;
        let mut terms = vec![first];

        while self.eat(&Token::OrOr) {
            terms.push(self.parse_and()?);
        }

        if terms.len() == 1 {
            Ok(terms.pop().expect("invariant: non-empty"))
        } else {
            Ok(canonical_or(terms))
        }
    }

    fn parse_and(&mut self) -> Result<Formula, SpecParseError> {
        let first = self.parse_comparison()?;
        let mut terms = vec![first];

        while self.eat(&Token::AndAnd) {
            terms.push(self.parse_comparison()?);
        }

        if terms.len() == 1 {
            Ok(terms.pop().expect("invariant: non-empty"))
        } else {
            Ok(canonical_and(terms))
        }
    }

    fn parse_comparison(&mut self) -> Result<Formula, SpecParseError> {
        let lhs = self.parse_add_sub()?;

        let op = match self.peek() {
            Some(Token::Gt) => CmpOp::Gt,
            Some(Token::Ge) => CmpOp::Ge,
            Some(Token::Lt) => CmpOp::Lt,
            Some(Token::Le) => CmpOp::Le,
            Some(Token::EqEq) => CmpOp::Eq,
            Some(Token::Ne) => CmpOp::Ne,
            _ => return Ok(lhs),
        };
        self.bump()?;
        let rhs = self.parse_add_sub()?;
        // A field/param var lexes at the parser's default `Int` sort; when it is
        // compared against a FLOAT literal the comparison is over f64, so re-sort a
        // bare integer Var operand to Float64 to match the f64 field it denotes.
        let (lhs, rhs) = coerce_float_comparison_operands(lhs, rhs);
        Ok(match op {
            CmpOp::Gt => Formula::Gt(Box::new(lhs), Box::new(rhs)),
            CmpOp::Ge => Formula::Ge(Box::new(lhs), Box::new(rhs)),
            CmpOp::Lt => Formula::Lt(Box::new(lhs), Box::new(rhs)),
            CmpOp::Le => Formula::Le(Box::new(lhs), Box::new(rhs)),
            CmpOp::Eq => Formula::Eq(Box::new(lhs), Box::new(rhs)),
            CmpOp::Ne => Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs)))),
        })
    }

    fn parse_add_sub(&mut self) -> Result<Formula, SpecParseError> {
        let mut expr = self.parse_mul_div()?;

        loop {
            if self.eat(&Token::Plus) {
                let rhs = self.parse_mul_div()?;
                expr = Formula::Add(Box::new(expr), Box::new(rhs));
            } else if self.eat(&Token::Minus) {
                let rhs = self.parse_mul_div()?;
                expr = Formula::Sub(Box::new(expr), Box::new(rhs));
            } else {
                return Ok(expr);
            }
        }
    }

    fn parse_mul_div(&mut self) -> Result<Formula, SpecParseError> {
        let mut expr = self.parse_unary()?;

        loop {
            if self.eat(&Token::Star) {
                let rhs = self.parse_unary()?;
                expr = Formula::Mul(Box::new(expr), Box::new(rhs));
            } else if self.eat(&Token::Slash) {
                let rhs = self.parse_unary()?;
                expr = Formula::Div(Box::new(expr), Box::new(rhs));
            } else if self.eat(&Token::Percent) {
                let rhs = self.parse_unary()?;
                expr = Formula::Rem(Box::new(expr), Box::new(rhs));
            } else {
                return Ok(expr);
            }
        }
    }

    fn parse_unary(&mut self) -> Result<Formula, SpecParseError> {
        if self.eat(&Token::Bang) {
            let expr = self.parse_unary()?;
            Ok(Formula::Not(Box::new(expr)))
        } else if self.eat(&Token::Minus) {
            let expr = self.parse_unary()?;
            // `-<float literal>` folds into a sign-flipped f64 const so it stays
            // Float-sorted. A plain `Neg` is Int-sorted (`infer_sort`), which would
            // mis-sort the lower half of a two-sided float magnitude bound
            // (`self.0 >= -1.0e30`) and defeat the well-sorted caller obligation.
            if let Formula::FpConst { bits, eb, sb } = expr {
                let negated = (-f64::from_bits(bits as u64)).to_bits();
                return Ok(Formula::FpConst { bits: u128::from(negated), eb, sb });
            }
            Ok(Formula::Neg(Box::new(expr)))
        } else if self.eat(&Token::Star) {
            // Trust: prefix `*x` dereferences a reference in a contract predicate
            // (`#[requires(*a <= 100)]` where `a: &u32`). The body's canonical place
            // naming renders a leading `Deref` projection as a SUFFIX `*`
            // (`place_to_var_name`: `*a` on a reference PARAMETER cannot be folded to
            // a referent, so it is named `"a*"`), so a spec `*a` must lower to
            // `Var("a*")` to unify with the body value. A prefix `*` only reaches
            // `parse_unary` at the START of an operand — infix multiply is consumed
            // by `parse_mul_div`'s loop — so any `Star` seen here is a deref. Only a
            // deref of a variable is modeled; `*(expr)` has no stable place name.
            let inner = self.parse_unary()?;
            match inner {
                // The high-level AST cannot currently retain a dereference of
                // the distinguished `result` node without losing provenance
                // into a user-constructible Var.  Reject it in both public
                // parsers until dereferenced return places have a typed node.
                Formula::Var(name, _) if name == "_0" => Err(SpecParseError::UnexpectedToken {
                    position: self.index.saturating_sub(1),
                    expected: "a named parameter, not result, after prefix '*'".into(),
                }),
                Formula::Var(name, sort)
                    if is_plain_source_binding_name(name.trim_end_matches('*')) =>
                {
                    Ok(Formula::Var(format!("{name}*"), sort))
                }
                _ => Err(SpecParseError::UnexpectedToken {
                    position: self.index.saturating_sub(1),
                    expected: "a plain named parameter after prefix '*' (deref)".into(),
                }),
            }
        } else {
            self.parse_postfix()
        }
    }

    fn parse_postfix(&mut self) -> Result<Formula, SpecParseError> {
        let mut expr = self.parse_atom()?;

        loop {
            // Handle dot-access: arr.len(), s.is_empty(), tuple index `t.0`.
            if self.eat(&Token::Dot) {
                let method = match self.bump()? {
                    Token::Ident(name) => name,
                    // Trust: numeric tuple-field projection `t.0` / `ret.1`. The MIR
                    // names a tuple/struct `Field(i)` projection `<base>.i`
                    // (`place_to_var_name`), so `ret.0` must lower to `Var("_0.0")` to
                    // unify with the return value's first component. A numeric field is
                    // never a method call (there is no `t.0()` form), so it takes the
                    // field-projection path directly. Over-refutation audit defect #2.
                    Token::Int(index) => {
                        expr = field_projection(
                            expr,
                            &index.to_string(),
                            self.index.saturating_sub(1),
                        )?;
                        continue;
                    }
                    _ => {
                        return Err(SpecParseError::UnexpectedToken {
                            position: self.index.saturating_sub(1),
                            expected: "field name or tuple index after '.'".into(),
                        });
                    }
                };

                // `base.method()` (parenthesized) maps a known method to a formula op;
                // `base.field` (no parens) is a general field projection → the synthetic
                // variable `base.field`, matching the MIR Adt-field extraction's naming
                // so a postcondition `ret == p.value` and the return `p.value` unify.
                if self.eat(&Token::LParen) {
                    self.expect(&Token::RParen, "')' after method call")?;
                    expr = map_method_call(expr, &method)?;
                } else {
                    expr = field_projection(expr, &method, self.index.saturating_sub(1))?;
                }
                continue;
            }
            // Keep the executable Formula parser in lockstep with the public
            // high-level AST parser. A literal index of a stable place uses the
            // canonical MIR projection spelling (`self.0[3]`), allowing a
            // following field projection to bind the exact body leaf. General
            // computed indexing remains an injective `Select`; it is never
            // collapsed into a free projected name.
            if self.eat(&Token::LBracket) {
                let index = self.parse_implies()?;
                self.expect(&Token::RBracket, "closing ']'")?;
                expr = match (expr, index) {
                    (Formula::Var(name, sort), Formula::Int(index)) if index >= 0 => {
                        Formula::Var(format!("{name}[{index}]"), sort)
                    }
                    (base, index) => Formula::Select(Box::new(base), Box::new(index)),
                };
                continue;
            }

            return Ok(expr);
        }
    }

    fn parse_atom(&mut self) -> Result<Formula, SpecParseError> {
        match self.bump()? {
            Token::Ident(name) => self.parse_ident(name),
            Token::Int(value) => Ok(Formula::Int(value)),
            // An f64 literal → the SMT FloatingPoint constant (binary64 format
            // `{ eb: 11, sb: 53 }`). Its bits round-trip exactly through the token.
            Token::Float(bits) => Ok(Formula::FpConst { bits: u128::from(bits), eb: 11, sb: 53 }),
            Token::LParen => {
                let expr = self.parse_implies()?;
                self.expect(&Token::RParen, "closing ')'")?;
                Ok(expr)
            }
            _ => Err(SpecParseError::UnexpectedToken {
                position: self.index.saturating_sub(1),
                expected: "identifier, integer, or '('".into(),
            }),
        }
    }

    fn parse_ident(&mut self, name: String) -> Result<Formula, SpecParseError> {
        if self.peek() == Some(&Token::Colon) {
            self.expect(&Token::Colon, "first ':' in associated constant")?;
            self.expect(&Token::Colon, "second ':' in associated constant")?;
            let constant = match self.bump()? {
                Token::Ident(constant) => constant,
                _ => {
                    return Err(SpecParseError::UnexpectedToken {
                        position: self.index.saturating_sub(1),
                        expected: "primitive integer associated constant name".into(),
                    });
                }
            };
            return primitive_integer_constant(&name, &constant).ok_or_else(|| {
                SpecParseError::UnexpectedToken {
                    position: self.index.saturating_sub(1),
                    expected: "fixed-width primitive integer MIN or MAX".into(),
                }
            });
        }

        match name.as_str() {
            "true" => Ok(Formula::Bool(true)),
            "false" => Ok(Formula::Bool(false)),
            "result" => Ok(self.variable(&name)),
            "old" if self.eat(&Token::LParen) => {
                let inner = match self.bump()? {
                    Token::Ident(inner) => inner,
                    _ => {
                        return Err(SpecParseError::UnexpectedToken {
                            position: self.index.saturating_sub(1),
                            expected: "variable name inside old()".into(),
                        });
                    }
                };
                if !is_plain_source_binding_name(&inner) {
                    return Err(SpecParseError::UnexpectedToken {
                        position: self.index.saturating_sub(1),
                        expected: "a non-reserved plain source binding inside old()".into(),
                    });
                }
                self.expect(&Token::RParen, "closing ')' for old()")?;
                Ok(int_var(format!("old_{inner}")))
            }
            "forall" if matches!(self.peek(), Some(Token::Ident(_))) => {
                self.parse_typed_quantifier(true)
            }
            "exists" if matches!(self.peek(), Some(Token::Ident(_))) => {
                self.parse_typed_quantifier(false)
            }
            "forall" if self.peek() == Some(&Token::LParen) => self.parse_compat_quantifier(true),
            "exists" if self.peek() == Some(&Token::LParen) => self.parse_compat_quantifier(false),
            // Trust SAFE_API §3.4: a closed-vocabulary predicate name followed
            // by `(` parses as an uninterpreted Pred application. Gated on
            // PRED_VOCAB membership so only reviewed names can ever become a
            // Pred; an out-of-vocab ident keeps today's behavior (a free Var,
            // with `(` left to fail downstream — never a silent Pred).
            _ if self.peek() == Some(&Token::LParen) && pred_arg_sorts(&name).is_some() => {
                self.parse_pred_call(name)
            }
            _ if is_plain_source_binding_name(&name) => Ok(self.variable(&name)),
            _ => Err(SpecParseError::UnexpectedToken {
                position: self.index.saturating_sub(1),
                expected: "a non-reserved plain source binding".into(),
            }),
        }
    }

    fn variable(&self, name: &str) -> Formula {
        let mapped = map_var_name(name);
        let sort = self
            .bound_sorts
            .iter()
            .rev()
            .find_map(|(bound, sort)| (bound == name).then(|| sort.clone()))
            .unwrap_or(Sort::Int);
        Formula::Var(mapped, sort)
    }

    /// Parse a vocabulary-gated uninterpreted predicate application
    /// `name(arg0, arg1, ...)` into `Formula::Pred(intern(name), [args])`.
    ///
    /// The caller's routing guard guarantees `name` is in PRED_VOCAB. Here we
    /// additionally reject a wrong arity (a hard parse error, never a silent
    /// accept) and re-key each argument to its declared sort.
    fn parse_pred_call(&mut self, name: String) -> Result<Formula, SpecParseError> {
        let sorts = pred_arg_sorts(&name)
            .expect("parse_pred_call is only reached for in-vocabulary predicate names");

        self.expect(&Token::LParen, &format!("'(' after predicate {name}"))?;

        let mut args = Vec::new();
        // Zero-arity predicates (e.g. `priv_dropped()`) close immediately.
        if self.peek() != Some(&Token::RParen) {
            loop {
                args.push(self.parse_implies()?);
                if !self.eat(&Token::Comma) {
                    break;
                }
            }
        }
        self.expect(&Token::RParen, &format!("closing ')' for predicate {name}"))?;

        if !is_valid_pred(&name, args.len()) {
            return Err(SpecParseError::InvalidQuantifier {
                detail: format!(
                    "predicate `{name}` expects {} argument(s), got {}",
                    sorts.len(),
                    args.len()
                ),
            });
        }

        // Re-key each argument to its declared sort (the default ladder produces
        // Sort::Int leaf Vars; PRED_VOCAB declares the true sort).
        let args = args
            .into_iter()
            .zip(sorts.iter().cloned())
            .map(|(arg, sort)| resort_pred_arg(arg, sort))
            .collect();

        Ok(Formula::Pred(crate::Symbol::intern(&name), args))
    }

    /// Parse `forall(var, lo..hi, body)` or `exists(var, lo..hi, body)`.
    ///
    /// Desugars into:
    /// - `forall(i, lo..hi, P(i))` => `Forall([(i, Int)], Implies(lo <= i && i < hi, P(i)))`
    /// - `exists(i, lo..hi, P(i))` => `Exists([(i, Int)], And(lo <= i, i < hi, P(i)))`
    fn parse_compat_quantifier(&mut self, is_forall: bool) -> Result<Formula, SpecParseError> {
        let label = if is_forall { "forall" } else { "exists" };

        self.expect(&Token::LParen, &format!("'(' after {label}"))?;

        // Parse bound variable name
        let var_name = match self.bump()? {
            Token::Ident(name) => name,
            _ => {
                return Err(SpecParseError::InvalidQuantifier {
                    detail: format!("{label}: expected variable name"),
                });
            }
        };
        if !is_plain_source_binding_name(&var_name) {
            return Err(SpecParseError::InvalidQuantifier {
                detail: format!("{label}: invalid or reserved binder `{var_name}`"),
            });
        }

        // Parenthesized typed spelling is accepted by the public high-level
        // attribute AST.  Give it the exact same executable meaning here,
        // rather than routing every `forall(` through the legacy range grammar.
        if self.eat(&Token::Colon) {
            let ty = match self.bump()? {
                Token::Ident(ty) => ty,
                _ => {
                    return Err(SpecParseError::InvalidQuantifier {
                        detail: format!("{label}: expected a scalar type name"),
                    });
                }
            };
            let (sort, domain) = typed_quantifier_domain(&ty, is_forall).ok_or_else(|| {
                SpecParseError::InvalidQuantifier {
                    detail: format!("{label}: unsupported binder type `{ty}`"),
                }
            })?;
            self.expect(&Token::Comma, &format!("',' after binder type in {label}"))?;

            let scope_len = self.bound_sorts.len();
            self.bound_sorts.push((var_name.clone(), sort.clone()));
            let parsed_body = self.parse_implies();
            self.bound_sorts.truncate(scope_len);
            let mut body = parsed_body?;
            self.expect(&Token::RParen, &format!("closing ')' for {label}"))?;

            if let Some(domain) = domain {
                let guard = domain.guard(Formula::Var(var_name.clone(), sort.clone()));
                body = if is_forall {
                    Formula::Implies(Box::new(guard), Box::new(body))
                } else {
                    canonical_and(vec![guard, body])
                };
            }
            let bindings = vec![(crate::Symbol::intern(&var_name), sort)];
            return Ok(if is_forall {
                Formula::Forall(bindings, Box::new(body))
            } else {
                Formula::Exists(bindings, Box::new(body))
            });
        }

        self.expect(&Token::Comma, &format!("',' or ':' after variable in {label}"))?;

        // Parse range: lo..hi
        let lo = self.parse_add_sub()?;
        if !self.eat(&Token::DotDot) {
            return Err(SpecParseError::InvalidQuantifier {
                detail: format!("{label}: expected '..' in range"),
            });
        }
        let hi = self.parse_add_sub()?;

        self.expect(&Token::Comma, &format!("',' after range in {label}"))?;

        // Parse the body with the compatibility binder in lexical scope.  The
        // explicit Int entry matters when this quantifier shadows an outer
        // Bool binding with the same name.
        let scope_len = self.bound_sorts.len();
        self.bound_sorts.push((var_name.clone(), Sort::Int));
        let parsed_body = self.parse_implies();
        self.bound_sorts.truncate(scope_len);
        let body = parsed_body?;

        self.expect(&Token::RParen, &format!("closing ')' for {label}"))?;

        let bound_var = Formula::Var(var_name.clone(), Sort::Int);
        let bindings = vec![(crate::Symbol::intern(&var_name), Sort::Int)];

        // Build range guard: lo <= var && var < hi
        let range_guard = Formula::And(vec![
            Formula::Le(Box::new(lo), Box::new(bound_var.clone())),
            Formula::Lt(Box::new(bound_var), Box::new(hi)),
        ]);

        if is_forall {
            // forall: range_guard => body
            Ok(Formula::Forall(
                bindings,
                Box::new(Formula::Implies(Box::new(range_guard), Box::new(body))),
            ))
        } else {
            // exists: range_guard && body
            Ok(Formula::Exists(bindings, Box::new(canonical_and(vec![range_guard, body]))))
        }
    }

    /// Parse the ratified first-class binder grammar:
    /// `forall i j: usize, P` / `exists x: bool, P`.
    ///
    /// The formula vocabulary has primitive SMT sorts rather than a Rust type
    /// context. Supported scalar type names therefore elaborate here; an
    /// unknown/user-defined type is rejected fail-closed and must be handled by
    /// the future typed frontend elaborator instead of guessed as `Int`.
    fn parse_typed_quantifier(&mut self, is_forall: bool) -> Result<Formula, SpecParseError> {
        let label = if is_forall { "forall" } else { "exists" };
        let mut names = Vec::new();
        while let Some(Token::Ident(_)) = self.peek() {
            let Token::Ident(name) = self.bump()? else { unreachable!() };
            if !is_plain_source_binding_name(&name) || names.contains(&name) {
                return Err(SpecParseError::InvalidQuantifier {
                    detail: format!("{label}: invalid or duplicate binder `{name}`"),
                });
            }
            names.push(name);
            if self.peek() == Some(&Token::Colon) {
                break;
            }
        }
        if names.is_empty() {
            return Err(SpecParseError::InvalidQuantifier {
                detail: format!("{label}: expected a binder name"),
            });
        }
        self.expect(&Token::Colon, &format!("':' after binders in {label}"))?;
        let ty = match self.bump()? {
            Token::Ident(ty) if !ty.contains('\'') => ty,
            _ => {
                return Err(SpecParseError::InvalidQuantifier {
                    detail: format!("{label}: expected a scalar type name"),
                });
            }
        };
        let (sort, domain) = typed_quantifier_domain(&ty, is_forall).ok_or_else(|| {
            SpecParseError::InvalidQuantifier {
                detail: format!("{label}: unsupported binder type `{ty}`"),
            }
        })?;
        self.expect(&Token::Comma, &format!("',' after binder type in {label}"))?;

        let scope_len = self.bound_sorts.len();
        self.bound_sorts.extend(names.iter().cloned().map(|name| (name, sort.clone())));
        let parsed_body = self.parse_implies();
        self.bound_sorts.truncate(scope_len);
        let mut body = parsed_body?;

        // Canonicalize grouped source binders to nested single-binding Formula
        // nodes.  `SpecExpr` uses that representation too, so grouped and
        // explicitly nested spellings now have one structural identity across
        // both public parsers (and therefore one digest).
        for name in names.into_iter().rev() {
            if let Some(domain_kind) = domain {
                let guard = domain_kind.guard(Formula::Var(name.clone(), sort.clone()));
                body = if is_forall {
                    Formula::Implies(Box::new(guard), Box::new(body))
                } else {
                    canonical_and(vec![guard, body])
                };
            }
            let bindings = vec![(crate::Symbol::intern(&name), sort.clone())];
            body = if is_forall {
                Formula::Forall(bindings, Box::new(body))
            } else {
                Formula::Exists(bindings, Box::new(body))
            };
        }
        Ok(body)
    }
}

#[derive(Copy, Clone)]
pub(crate) enum QuantifierDomain {
    NonNegative,
    Inclusive { min: i128, max: i128 },
    UnsignedInclusive { max: u128 },
}

impl QuantifierDomain {
    pub(crate) fn guard(self, variable: Formula) -> Formula {
        match self {
            Self::NonNegative => Formula::Ge(Box::new(variable), Box::new(Formula::Int(0))),
            Self::Inclusive { min, max } => Formula::And(vec![
                Formula::Ge(Box::new(variable.clone()), Box::new(Formula::Int(min))),
                Formula::Le(Box::new(variable), Box::new(Formula::Int(max))),
            ]),
            Self::UnsignedInclusive { max } => Formula::And(vec![
                Formula::Ge(Box::new(variable.clone()), Box::new(Formula::Int(0))),
                Formula::Le(Box::new(variable), Box::new(Formula::UInt(max))),
            ]),
        }
    }
}

pub(crate) fn typed_quantifier_domain(
    ty: &str,
    is_forall: bool,
) -> Option<(Sort, Option<QuantifierDomain>)> {
    let int = |domain| Some((Sort::Int, domain));
    match ty {
        "bool" => Some((Sort::Bool, None)),
        "int" => int(None),
        "nat" => int(Some(QuantifierDomain::NonNegative)),
        "i8" => int(Some(QuantifierDomain::Inclusive { min: i8::MIN.into(), max: i8::MAX.into() })),
        "i16" => {
            int(Some(QuantifierDomain::Inclusive { min: i16::MIN.into(), max: i16::MAX.into() }))
        }
        "i32" => {
            int(Some(QuantifierDomain::Inclusive { min: i32::MIN.into(), max: i32::MAX.into() }))
        }
        "i64" => {
            int(Some(QuantifierDomain::Inclusive { min: i64::MIN.into(), max: i64::MAX.into() }))
        }
        "i128" => int(Some(QuantifierDomain::Inclusive { min: i128::MIN, max: i128::MAX })),
        "u8" => int(Some(QuantifierDomain::UnsignedInclusive { max: u8::MAX.into() })),
        "u16" => int(Some(QuantifierDomain::UnsignedInclusive { max: u16::MAX.into() })),
        "u32" => int(Some(QuantifierDomain::UnsignedInclusive { max: u32::MAX.into() })),
        "u64" => int(Some(QuantifierDomain::UnsignedInclusive { max: u64::MAX.into() })),
        "u128" => int(Some(QuantifierDomain::UnsignedInclusive { max: u128::MAX })),
        // The target-independent parser cannot know pointer width. Universal
        // quantification over the mathematical super-domain is conservative;
        // existential quantification would be unsound (it could choose a value
        // absent from the target), so it is rejected until target-aware typed
        // elaboration supplies the exact range.
        "usize" if is_forall => int(Some(QuantifierDomain::NonNegative)),
        "isize" if is_forall => int(None),
        _ => None,
    }
}

/// Map a method call on a formula to the appropriate representation.
///
/// Known methods:
/// - `.len()` => `Var("<base>_len", Int)` (models collection length)
/// - `.is_empty()` => `Eq(<base>_len, 0)` (models emptiness check)
pub(crate) fn map_method_call(base: Formula, method: &str) -> Result<Formula, SpecParseError> {
    let base_name = match &base {
        Formula::Var(name, _) => name.clone(),
        _ => return Err(SpecParseError::UnsupportedMethod { method: method.into() }),
    };

    match method {
        "len" => Ok(int_var(format!("{base_name}_len"))),
        "is_empty" => Ok(Formula::Eq(
            Box::new(int_var(format!("{base_name}_len"))),
            Box::new(Formula::Int(0)),
        )),
        // Trust SAFE_API §3.4: the fixed capability accessor set. `.fd()` /
        // `.components()` lower to the handle's stable ghost-identity term — a
        // Var keyed to the handle binding, identical to the bare handle — so
        // `dir_open(dir.fd())` and `dir_open(dir)` produce the same Pred arg.
        // This is a CLOSED set; general field projection stays unsupported.
        "fd" | "components" => Ok(int_var(base_name)),
        // Option-result reasoning for postconditions of `Option<T>`-returning
        // functions, e.g. `result.is_none() || result.unwrap() < n`. The
        // discriminant `{base}_discr` (0 = None) and payload `{base}_value`
        // model the wrapper. The VC layer is responsible for linking these to the
        // actual return: until it does they are free variables, so such a
        // postcondition can only FAIL to prove, never vacuously prove
        // (fail-closed). Before this, `is_none`/`is_some`/`unwrap` returned
        // `UnsupportedMethod`, which `parse_spec_expr` swallows to `None`,
        // SILENTLY DROPPING the entire contract (no VC emitted) — a
        // false-success hazard that this closes.
        "is_none" => Ok(Formula::Eq(
            Box::new(int_var(format!("{base_name}_discr"))),
            Box::new(Formula::Int(0)),
        )),
        "is_some" => Ok(Formula::Not(Box::new(Formula::Eq(
            Box::new(int_var(format!("{base_name}_discr"))),
            Box::new(Formula::Int(0)),
        )))),
        "unwrap" => Ok(int_var(format!("{base_name}_value"))),
        // Result reasoning, mirroring the Option discriminant/value model above.
        // We adopt the SAME convention as Option (`_discr == 0` = the "empty"
        // variant): for a Result, `_discr == 0` models the `Err` variant and a
        // nonzero discriminant models `Ok`. This keeps `is_ok`/`is_err` the exact
        // boolean duals of `is_some`/`is_none`, and reuses `{base}_value` (already
        // the `unwrap` payload term) as the Ok payload — so `result.is_ok()` and
        // `result.unwrap()` ground to the same `{base}_discr`/`{base}_value` pair.
        //
        // SEMANTICS:
        //   is_ok  => `{base}_discr != 0`   (the Result is the Ok variant)
        //   is_err => `{base}_discr == 0`   (the Result is the Err variant)
        // As with Option, the VC layer is responsible for linking these synthetic
        // terms to the actual return value; until it does they are free variables,
        // so such a postcondition can only FAIL to prove, never vacuously prove
        // (fail-closed). Previously these returned UnsupportedMethod, which
        // `parse_spec_expr` swallows to None — silently dropping the whole contract.
        "is_ok" => Ok(Formula::Not(Box::new(Formula::Eq(
            Box::new(int_var(format!("{base_name}_discr"))),
            Box::new(Formula::Int(0)),
        )))),
        "is_err" => Ok(Formula::Eq(
            Box::new(int_var(format!("{base_name}_discr"))),
            Box::new(Formula::Int(0)),
        )),
        // Sign predicates on an integer/rational base (e.g. `c.is_positive()` for
        // the rational `c` extracted from an Ok payload). We model the trichotomy
        // with ONE synthetic Int var `{base}_sign` that stands for the sign of the
        // base value (negative / zero / positive ↦ a value < 0 / == 0 / > 0).
        //
        // SEMANTICS:
        //   is_negative => `{base}_sign < 0`
        //   is_zero     => `{base}_sign == 0`
        //   is_positive => `{base}_sign > 0`
        // Because all three predicates refer to the SAME `{base}_sign` term, LIA
        // automatically gives the trichotomy and the mutual exclusion: e.g.
        // `!(c.is_positive())` (the negation of `{base}_sign > 0`, i.e.
        // `{base}_sign <= 0`) is exactly "c is negative or zero". This is the EXACT
        // boolean dual structure of the source `is_positive`/`is_negative`/`is_zero`
        // (each tests a distinct, mutually-exclusive, exhaustive branch of the sign).
        // The `{base}_sign` term is a free variable until the VC layer links it to
        // the base's concrete value, so a sign postcondition can only FAIL to prove,
        // never vacuously prove (fail-closed). Previously these returned
        // UnsupportedMethod, silently dropping the contract.
        "is_negative" => Ok(Formula::Lt(
            Box::new(int_var(format!("{base_name}_sign"))),
            Box::new(Formula::Int(0)),
        )),
        "is_zero" => Ok(Formula::Eq(
            Box::new(int_var(format!("{base_name}_sign"))),
            Box::new(Formula::Int(0)),
        )),
        "is_positive" => Ok(Formula::Gt(
            Box::new(int_var(format!("{base_name}_sign"))),
            Box::new(Formula::Int(0)),
        )),
        _ => Err(SpecParseError::UnsupportedMethod { method: method.into() }),
    }
}

/// A general field projection `base.field` → the synthetic variable
/// `base.field`. The MIR Adt-field extraction names a parameter's field
/// identically (`param.field`), so a postcondition referencing `p.value` and a
/// return of `p.value` unify to the same variable (provable by `Eq.refl`).
pub(crate) fn field_projection(
    base: Formula,
    field: &str,
    position: usize,
) -> Result<Formula, SpecParseError> {
    match base {
        Formula::Var(name, sort) => Ok(Formula::Var(format!("{name}.{field}"), sort)),
        _ => Err(SpecParseError::UnexpectedToken {
            position,
            expected: "a variable to project a field from".into(),
        }),
    }
}

/// The comparison operators `parse_comparison` dispatches on, so the shared
/// operand parsing + float-sort coercion runs once for all six.
enum CmpOp {
    Gt,
    Ge,
    Lt,
    Le,
    Eq,
    Ne,
}

/// The IEEE-754 binary64 sort (`f64`), the sort a spec float literal and a field
/// var compared against one take.
const F64_SORT: Sort = Sort::Float { eb: 11, sb: 53 };

/// Whether a formula leaf is IEEE-754 float-sorted — a float literal (`FpConst`)
/// or a `Float`-sorted variable.
fn is_float_sorted(f: &Formula) -> bool {
    matches!(f, Formula::FpConst { .. }) || matches!(f.var_sort(), Some(Sort::Float { .. }))
}

/// Re-sort a bare `Int`-defaulted variable operand to f64 when the OTHER operand
/// of a comparison is float-sorted, so `self.0 <= 1.0e30` binds the f64 field
/// `self.0` at Float64 (matching the body place `place_to_var_name` renders)
/// rather than the parser's default `Int`. Only a leaf `Var`/`SymVar` still at the
/// default `Int` sort is retyped; compound terms and already-typed leaves are left
/// untouched. Fail-closed: an un-retyped operand simply stays as parsed and cannot
/// manufacture a spuriously well-sorted match.
fn coerce_float_comparison_operands(lhs: Formula, rhs: Formula) -> (Formula, Formula) {
    fn resort_to_f64(f: Formula) -> Formula {
        match f {
            Formula::Var(name, Sort::Int) => Formula::Var(name, F64_SORT),
            Formula::SymVar(sym, Sort::Int) => Formula::SymVar(sym, F64_SORT),
            other => other,
        }
    }
    match (is_float_sorted(&lhs), is_float_sorted(&rhs)) {
        (true, false) => (lhs, resort_to_f64(rhs)),
        (false, true) => (resort_to_f64(lhs), rhs),
        _ => (lhs, rhs),
    }
}

fn int_var(name: String) -> Formula {
    Formula::Var(name, Sort::Int)
}

/// Build the parser's canonical n-ary conjunction while preserving authored
/// left-to-right order.  Flattening nested nodes makes parentheses around an
/// associative Boolean chain irrelevant to Formula identity.
pub(crate) fn canonical_and(items: Vec<Formula>) -> Formula {
    fn append(item: Formula, flat: &mut Vec<Formula>) {
        match item {
            Formula::And(nested) => {
                for item in nested {
                    append(item, flat);
                }
            }
            other => flat.push(other),
        }
    }

    let mut flat = Vec::new();
    for item in items {
        append(item, &mut flat);
    }
    Formula::And(flat)
}

/// Build the parser's canonical n-ary disjunction while preserving authored
/// left-to-right order.  See [`canonical_and`].
pub(crate) fn canonical_or(items: Vec<Formula>) -> Formula {
    fn append(item: Formula, flat: &mut Vec<Formula>) {
        match item {
            Formula::Or(nested) => {
                for item in nested {
                    append(item, flat);
                }
            }
            other => flat.push(other),
        }
    }

    let mut flat = Vec::new();
    for item in items {
        append(item, &mut flat);
    }
    Formula::Or(flat)
}

/// Apply a predicate argument's declared sort (from PRED_VOCAB) to a parsed
/// term. The default precedence ladder produces `Sort::Int` leaf Vars
/// (`int_var`); re-key a leaf Var to its declared sort so the EUF application is
/// well-sorted. Compound argument terms — not expected for capability
/// predicates, whose args are handle-keyed leaves — are passed through.
fn resort_pred_arg(arg: Formula, sort: Sort) -> Formula {
    match arg {
        Formula::Var(name, _) => Formula::Var(name, sort),
        other => other,
    }
}

/// The kind of synthetic solver name with which a Rust/source binding would
/// collide after contract lowering.
///
/// Contract formulas currently use a compact compatibility encoding:
/// `result` becomes `_0`, `old(x)` becomes `old_x`, modeled accessors mint
/// leaves ending in `_len`, `_discr`, `_value`, or `_sign`, and MIR/VC lowering
/// reserves double-underscore spellings for generated metadata (for example
/// `s__slice_len` and `__trust_constparam_0_N`).  Those spellings are legal
/// Rust identifiers, so admitting the same spelling as an ordinary binding
/// would make the lowering non-injective and could collapse a false relation
/// into reflexivity.  Keep this classification shared by every
/// source/query/extraction boundary until the formula vocabulary carries
/// tagged provenance directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceContractSyntheticNameCollision {
    /// The source `result` value and MIR return place `_0`.
    ReturnPlace,
    /// The compatibility pre-state spelling `old(<binding>)`.
    OldValue,
    /// A modeled accessor/projection leaf.
    Projection,
    /// A positional MIR local fallback such as `_1` or `_2`.
    PositionalPlace,
    /// A closed-vocabulary uninterpreted predicate symbol.
    PredicateSymbol,
    /// Compiler/VC-generated metadata. All source identifiers containing `__`
    /// are conservatively reserved so newly added generated leaves cannot
    /// silently reopen the namespace.
    GeneratedMetadata,
}

/// Whether `name` can denote one ordinary source binding at a contract
/// boundary without colliding with grammar keywords or generated Formula
/// symbols.
///
/// Keep this single predicate shared by `old(name)`, quantifier binders, and
/// the public high-level AST converter.  Accepting a reserved spelling at just
/// one of those entrances makes source-to-Formula lowering non-injective.
pub(crate) fn is_plain_source_binding_name(name: &str) -> bool {
    let mut bytes = name.bytes();
    let Some(first) = bytes.next() else { return false };
    (first == b'_' || first.is_ascii_alphabetic())
        && bytes.all(|byte| byte == b'_' || byte.is_ascii_alphanumeric())
        && !matches!(name, "true" | "false" | "result" | "forall" | "exists")
        && source_contract_synthetic_name_collision(name).is_none()
}

/// Classify a source binding that occupies the contract lowerer's synthetic
/// namespace.
///
/// Trailing `*` is ignored because exact source environments spell a scalar
/// reference binding `x` as `x*`.  Projection suffixes are deliberately
/// rejected independent of a currently visible base: quantifier binders can
/// introduce that base inside a clause, and chained accessors still end in one
/// of the same four suffixes.
pub fn source_contract_synthetic_name_collision(
    name: &str,
) -> Option<SourceContractSyntheticNameCollision> {
    let name = name.trim_end_matches('*');
    if matches!(name, "result" | "_0") {
        return Some(SourceContractSyntheticNameCollision::ReturnPlace);
    }
    if let Some(index) = name.strip_prefix('_')
        && !index.is_empty()
        && index.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Some(SourceContractSyntheticNameCollision::PositionalPlace);
    }
    if pred_arg_sorts(name).is_some() {
        return Some(SourceContractSyntheticNameCollision::PredicateSymbol);
    }
    // Trust's MIR/Formula producers reserve `__` for generated metadata:
    // `{place}__slice_len`, `__trust_constparam_*`, `__type_tag`, `__old`,
    // overflow/reification auxiliaries, and future additions.  Reserve the
    // whole family rather than chasing a perpetually incomplete prefix list.
    // This is intentionally conservative: legal Rust bindings in this family
    // are demoted to their injective per-local MIR spelling outside contracts
    // and rejected in source-contract scopes.
    if name.contains("__") {
        return Some(SourceContractSyntheticNameCollision::GeneratedMetadata);
    }
    if name.starts_with("old_") {
        return Some(SourceContractSyntheticNameCollision::OldValue);
    }
    if ["_len", "_discr", "_value", "_sign"].into_iter().any(|suffix| name.ends_with(suffix)) {
        return Some(SourceContractSyntheticNameCollision::Projection);
    }
    None
}

fn map_var_name(name: &str) -> String {
    if name == "result" { "_0".to_string() } else { name.to_string() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::SpecParseError;

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn int(value: i128) -> Formula {
        Formula::Int(value)
    }

    // === Backward-compatible tests (Option API) ===

    #[test]
    fn parses_simple_comparison() {
        let expected = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        assert_eq!(parse_spec_expr("x > 0"), Some(expected));
    }

    #[test]
    fn parses_field_magnitude_precondition_for_overflow_discharge() {
        // a3d-geom's float-overflow discharge keys the operand name
        // `place_to_var_name` produces — `self.0` (Field INDEX 0), never `self.x` —
        // against a `#[requires]` magnitude bound. This LOCKS the exact lowering the
        // discharge in trust-vcgen depends on: a flat `And` of `Le`/`Ge` over the
        // index-named field var, with `-C` lowered to `Neg(Int(C))`. A drift here
        // (e.g. emitting `Var("self.x")`) would silently unbind the discharge.
        let c = 1_000_000_000_000_000_000i128;
        let expected = Formula::And(vec![
            Formula::Le(Box::new(var("self.0")), Box::new(int(c))),
            Formula::Ge(Box::new(var("self.0")), Box::new(Formula::Neg(Box::new(int(c))))),
        ]);
        assert_eq!(
            parse_spec_expr("self.0 <= 1000000000000000000 && self.0 >= -1000000000000000000"),
            Some(expected),
        );
    }

    #[test]
    fn parses_shared_ref_field_projection_to_deref_field_name() {
        // A `&self` field (`Transform::compose`'s `self.scale`) is `(*self).2` in
        // MIR, which `place_to_var_name` renders "self*.2" (leading `Deref` => "*",
        // then `Field(2)` => ".2"). The contract must spell it `(*self).2` to unify
        // byte-for-byte; the by-NAME `self.x` form yields a distinct "self.x" var.
        assert_eq!(
            parse_spec_expr("(*self).2 <= 100"),
            Some(Formula::Le(Box::new(var("self*.2")), Box::new(int(100)))),
        );
        assert_eq!(
            parse_spec_expr("self.x <= 100"),
            Some(Formula::Le(Box::new(var("self.x")), Box::new(int(100)))),
        );
    }

    #[test]
    fn parses_literal_array_index_segments_into_var_names() {
        // `p[3]` / `self.0[3].1` — a LITERAL index appends a `[k]` segment to the
        // projected var name, the contract-side canonical spelling the vcgen float
        // lane matches against (after canonicalizing its `[k;min=L]` body render).
        assert_eq!(parse_spec_expr("x[0]"), Some(var("x[0]")));
        assert_eq!(parse_spec_expr("self.0[3].1"), Some(var("self.0[3].1")));
        // Index segments compose with comparisons and further projections.
        assert_eq!(
            parse_spec_expr("x[0] <= 5"),
            Some(Formula::Le(Box::new(var("x[0]")), Box::new(int(5)))),
        );
        assert_eq!(parse_spec_expr("x[0][1]"), Some(var("x[0][1]")));
    }

    #[test]
    fn literal_array_index_var_coerces_to_float_against_float_literal() {
        // The a3d bracketed-chain magnitude bound: the indexed var re-sorts to f64
        // when compared against an f64 literal, exactly like a dotted field var.
        assert_eq!(
            parse_spec_expr("(self.0[0]) <= (1.0e30)"),
            Some(Formula::Le(Box::new(f64_var("self.0[0]")), Box::new(fp(1.0e30_f64)))),
        );
    }

    #[test]
    fn computed_array_indices_remain_structural_selects() {
        // A computed index is never collapsed into a synthetic free place name.
        // It retains the exact `Select` structure shared with the public AST
        // lowering, so downstream unsupported cases can fail closed without an
        // injectivity or parser-parity loss.
        assert_eq!(
            parse_spec_expr_result("x[i]").unwrap(),
            Formula::Select(Box::new(var("x")), Box::new(var("i"))),
        );
        assert!(matches!(parse_spec_expr_result("x[i+1]").unwrap(), Formula::Select(_, _)));
    }

    #[test]
    fn rejects_malformed_array_indices() {
        // An unclosed bracket and a bare `[0]` have no well-formed source AST.
        for input in ["x[0", "[0]"] {
            assert_eq!(parse_spec_expr(input), None, "input must fail: {input}");
        }
    }

    fn f64_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Float { eb: 11, sb: 53 })
    }
    fn fp(v: f64) -> Formula {
        Formula::FpConst { bits: u128::from(v.to_bits()), eb: 11, sb: 53 }
    }

    #[test]
    fn parses_float_magnitude_precondition_as_float_sorted() {
        // `self.0 <= 1.0e30 && self.0 >= -1.0e30` — the a3d float-overflow magnitude
        // bound. The field var re-sorts to f64 (matching the field it denotes), the
        // literal is a binary64 `FpConst`, and the negative half folds into a signed
        // `FpConst` (NOT `Neg`, which would be Int-sorted and mis-typed).
        let c = 1.0e30_f64;
        let expected = Formula::And(vec![
            Formula::Le(Box::new(f64_var("self.0")), Box::new(fp(c))),
            Formula::Ge(Box::new(f64_var("self.0")), Box::new(fp(-c))),
        ]);
        assert_eq!(parse_spec_expr("self.0 <= 1.0e30 && self.0 >= -1.0e30"), Some(expected),);
    }

    #[test]
    fn float_literal_spellings_all_lex_to_fp_const() {
        // `1e30`, `1.0e30`, and the fully-written-out integer-with-point all denote
        // the same f64 and must lex+parse as a `FpConst` bound (never `Int` + junk).
        for spelling in ["1e30", "1.0e30", "1000000000000000000000000000000.0"] {
            let parsed = parse_spec_expr(&format!("self.0 <= {spelling}"));
            assert_eq!(
                parsed,
                Some(Formula::Le(Box::new(f64_var("self.0")), Box::new(fp(1.0e30_f64)))),
                "spelling {spelling} must parse as an f64 bound",
            );
        }
        // Exponent sign variants and a plain decimal too.
        assert_eq!(
            parse_spec_expr("x <= 2.5e-3"),
            Some(Formula::Le(Box::new(f64_var("x")), Box::new(fp(2.5e-3_f64)))),
        );
        assert_eq!(
            parse_spec_expr("x <= 3.14"),
            Some(Formula::Le(Box::new(f64_var("x")), Box::new(fp(3.14_f64)))),
        );
    }

    #[test]
    fn integer_literals_and_range_dots_are_unaffected_by_float_lexing() {
        // A bare integer stays `Int`; `t.0` (tuple field after an ident) stays a
        // field projection; `0..n` stays integer + `DotDot`. Regression-guards that
        // the float lexer's `.`/`e` lookahead does not swallow these.
        assert_eq!(
            parse_spec_expr("x > 0"),
            Some(Formula::Gt(Box::new(var("x")), Box::new(int(0))))
        );
        assert_eq!(
            parse_spec_expr("t.0 <= 5"),
            Some(Formula::Le(Box::new(var("t.0")), Box::new(int(5)))),
        );
        // `forall(i, 0..n, i < n)` exercises `0..` — must not become a float.
        assert!(parse_spec_expr("forall(i, 0..n, i < n)").is_some());
    }

    #[test]
    fn parses_result_mapping_and_arithmetic() {
        let expected = Formula::Ge(
            Box::new(var("_0")),
            Box::new(Formula::Add(Box::new(var("a")), Box::new(var("b")))),
        );

        assert_eq!(parse_spec_expr("result >= a + b"), Some(expected));
    }

    #[test]
    fn parses_option_result_postcondition() {
        // Regression: `is_none`/`unwrap` used to return UnsupportedMethod, which
        // `parse_spec_expr` swallowed to None — SILENTLY DROPPING the contract of
        // every Option-returning fn (no VC). They must now parse: discriminant
        // `_0_discr` (0 = None) and payload `_0_value`.
        let parsed = parse_spec_expr("result.is_none() || result.unwrap() < n")
            .expect("Option-result postcondition must parse (not silently drop)");
        let expected = Formula::Or(vec![
            Formula::Eq(Box::new(var("_0_discr")), Box::new(int(0))),
            Formula::Lt(Box::new(var("_0_value")), Box::new(var("n"))),
        ]);
        assert_eq!(parsed, expected);
        // is_some is the negation of the discriminant-is-zero test.
        assert_eq!(
            parse_spec_expr("result.is_some()"),
            Some(Formula::Not(Box::new(Formula::Eq(Box::new(var("_0_discr")), Box::new(int(0))))))
        );
    }

    #[test]
    fn parses_result_ok_err_postcondition() {
        // Result reasoning mirrors Option: `_discr == 0` = Err, nonzero = Ok, with
        // `{base}_value` as the Ok payload. These must parse (not silently drop the
        // contract of a Result-returning fn). `result` maps to `_0`.
        assert_eq!(
            parse_spec_expr("result.is_ok()"),
            Some(Formula::Not(Box::new(Formula::Eq(Box::new(var("_0_discr")), Box::new(int(0))))))
        );
        assert_eq!(
            parse_spec_expr("result.is_err()"),
            Some(Formula::Eq(Box::new(var("_0_discr")), Box::new(int(0))))
        );
        // `is_ok` is exactly the boolean dual of `is_err`.
        assert_eq!(parse_spec_expr("result.is_ok()"), parse_spec_expr("!(result.is_err())"));
    }

    #[test]
    fn parses_sign_predicates() {
        // `is_positive`/`is_negative`/`is_zero` model ONE synthetic sign var
        // `{base}_sign`; the trichotomy is then automatic LIA.
        assert_eq!(
            parse_spec_expr("c.is_positive()"),
            Some(Formula::Gt(Box::new(var("c_sign")), Box::new(int(0))))
        );
        assert_eq!(
            parse_spec_expr("c.is_negative()"),
            Some(Formula::Lt(Box::new(var("c_sign")), Box::new(int(0))))
        );
        assert_eq!(
            parse_spec_expr("c.is_zero()"),
            Some(Formula::Eq(Box::new(var("c_sign")), Box::new(int(0))))
        );
    }

    #[test]
    fn parses_chained_result_unwrap_sign() {
        // The exact checker idiom after lowering: the Ok payload extracted via
        // `unwrap` (→ `{base}_value`) then sign-tested. `result.unwrap()` →
        // `_0_value`, `.is_positive()` → `_0_value_sign > 0`. This is what
        // `!matches!(r, Ok(c) if c.is_positive())` lowers into (under the outer Not):
        // `!((result.is_ok()) && (result.unwrap().is_positive()))`.
        assert_eq!(
            parse_spec_expr("result.unwrap().is_positive()"),
            Some(Formula::Gt(Box::new(var("_0_value_sign")), Box::new(int(0))))
        );
        let parsed = parse_spec_expr("!((result.is_ok()) && (result.unwrap().is_positive()))")
            .expect("the lowered check_farkas postcondition must parse");
        let expected = Formula::Not(Box::new(Formula::And(vec![
            Formula::Not(Box::new(Formula::Eq(Box::new(var("_0_discr")), Box::new(int(0))))),
            Formula::Gt(Box::new(var("_0_value_sign")), Box::new(int(0))),
        ])));
        assert_eq!(parsed, expected);
    }

    #[test]
    fn parses_lowered_tuple_ok_postcondition() {
        // The exact lowered text for `check_entailment`/`check_chain`:
        // `!matches!(r, Ok((d, c)) if d > c)` ↦
        // `!((result.is_ok()) && (result.unwrap().__trust_ok_0 > result.unwrap().__trust_ok_1))`.
        // The two tuple binds become DISTINCT, STABLE field vars on the Ok payload.
        let parsed = parse_spec_expr(
            "!((result.is_ok()) && \
             (result.unwrap().__trust_ok_0 > result.unwrap().__trust_ok_1))",
        )
        .expect("the lowered check_entailment postcondition must parse");
        let expected = Formula::Not(Box::new(Formula::And(vec![
            Formula::Not(Box::new(Formula::Eq(Box::new(var("_0_discr")), Box::new(int(0))))),
            Formula::Gt(
                Box::new(var("_0_value.__trust_ok_0")),
                Box::new(var("_0_value.__trust_ok_1")),
            ),
        ])));
        assert_eq!(parsed, expected);
    }

    #[test]
    fn parses_not_equal_as_negated_equality() {
        let expected = Formula::Not(Box::new(Formula::Eq(Box::new(var("n")), Box::new(int(0)))));

        assert_eq!(parse_spec_expr("n != 0"), Some(expected));
    }

    #[test]
    fn parses_old_syntax() {
        let expected = Formula::Le(Box::new(var("old_x")), Box::new(var("_0")));
        assert_eq!(parse_spec_expr("old(x) <= result"), Some(expected));
    }

    #[test]
    fn old_is_only_special_when_called() {
        let expected = Formula::Add(Box::new(var("old")), Box::new(int(1)));
        assert_eq!(parse_spec_expr("old + 1"), Some(expected));
    }

    #[test]
    fn synthetic_contract_namespace_classifier_is_closed_over_accessor_chains() {
        use SourceContractSyntheticNameCollision as Collision;

        assert_eq!(
            source_contract_synthetic_name_collision("result"),
            Some(Collision::ReturnPlace)
        );
        assert_eq!(source_contract_synthetic_name_collision("_0"), Some(Collision::ReturnPlace));
        assert_eq!(source_contract_synthetic_name_collision("old_x"), Some(Collision::OldValue));
        assert_eq!(
            source_contract_synthetic_name_collision("_17"),
            Some(Collision::PositionalPlace)
        );
        assert_eq!(
            source_contract_synthetic_name_collision("priv_dropped"),
            Some(Collision::PredicateSymbol)
        );
        assert_eq!(
            source_contract_synthetic_name_collision("is_whnf"),
            Some(Collision::PredicateSymbol)
        );
        assert_eq!(
            source_contract_synthetic_name_collision("s__slice_len"),
            Some(Collision::GeneratedMetadata)
        );
        assert_eq!(
            source_contract_synthetic_name_collision("__trust_constparam_0_N"),
            Some(Collision::GeneratedMetadata)
        );
        assert_eq!(
            source_contract_synthetic_name_collision("value__future_metadata"),
            Some(Collision::GeneratedMetadata)
        );
        assert_eq!(source_contract_synthetic_name_collision("xs_len"), Some(Collision::Projection));
        assert_eq!(
            source_contract_synthetic_name_collision("x_discr"),
            Some(Collision::Projection)
        );
        assert_eq!(
            source_contract_synthetic_name_collision("x_value"),
            Some(Collision::Projection)
        );
        assert_eq!(
            source_contract_synthetic_name_collision("x_value_sign"),
            Some(Collision::Projection)
        );
        assert_eq!(
            source_contract_synthetic_name_collision("x_sign*"),
            Some(Collision::Projection)
        );
        assert_eq!(source_contract_synthetic_name_collision("payload_length"), None);
        assert_eq!(source_contract_synthetic_name_collision("older_x"), None);
    }

    #[test]
    fn quantifiers_reject_synthetic_contract_binders() {
        for name in [
            "result",
            "_0",
            "_2",
            "priv_dropped",
            "s__slice_len",
            "__trust_constparam_0_N",
            "old_x",
            "xs_len",
            "x_discr",
            "x_value",
            "x_sign",
            "x_value_sign",
        ] {
            let native = parse_spec_expr_result(&format!("forall {name}: u64, true"));
            assert!(
                matches!(native, Err(SpecParseError::InvalidQuantifier { .. })),
                "native binder `{name}` must fail closed, got {native:?}",
            );
            let compat = parse_spec_expr_result(&format!("forall({name}, 0..1, true)"));
            assert!(
                matches!(compat, Err(SpecParseError::InvalidQuantifier { .. })),
                "compat binder `{name}` must fail closed, got {compat:?}",
            );
        }
    }

    #[test]
    fn parses_boolean_literals_and_logical_precedence() {
        let expected = Formula::Or(vec![
            Formula::Gt(Box::new(var("a")), Box::new(int(0))),
            Formula::And(vec![
                Formula::Gt(Box::new(var("b")), Box::new(int(0))),
                Formula::Gt(Box::new(var("c")), Box::new(int(0))),
            ]),
        ]);

        assert_eq!(parse_spec_expr("a > 0 || b > 0 && c > 0"), Some(expected));
    }

    #[test]
    fn parses_parentheses_before_logical_ops() {
        let expected = Formula::And(vec![
            Formula::Or(vec![
                Formula::Gt(Box::new(var("a")), Box::new(int(0))),
                Formula::Gt(Box::new(var("b")), Box::new(int(0))),
            ]),
            Formula::Gt(Box::new(var("c")), Box::new(int(0))),
        ]);

        assert_eq!(parse_spec_expr("(a > 0 || b > 0) && c > 0"), Some(expected));
    }

    #[test]
    fn parses_implication_at_lowest_precedence() {
        let expected = Formula::Implies(
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(int(0)))),
            Box::new(Formula::Or(vec![
                Formula::Gt(Box::new(var("_0")), Box::new(var("x"))),
                Formula::Eq(Box::new(var("_0")), Box::new(var("x"))),
            ])),
        );

        assert_eq!(parse_spec_expr("x > 0 => result > x || result == x"), Some(expected));
    }

    #[test]
    fn parses_unary_not() {
        let expected = Formula::Not(Box::new(Formula::Eq(Box::new(var("x")), Box::new(int(0)))));

        assert_eq!(parse_spec_expr("!(x == 0)"), Some(expected));
    }

    #[test]
    fn parses_arithmetic_precedence_and_associativity() {
        let expected = Formula::Sub(
            Box::new(Formula::Add(
                Box::new(var("a")),
                Box::new(Formula::Mul(Box::new(var("b")), Box::new(var("c")))),
            )),
            Box::new(Formula::Div(Box::new(var("d")), Box::new(var("e")))),
        );

        assert_eq!(parse_spec_expr("a + b * c - d / e"), Some(expected));
    }

    #[test]
    fn parses_unary_minus() {
        let expected = Formula::Add(Box::new(Formula::Neg(Box::new(var("x")))), Box::new(int(1)));

        assert_eq!(parse_spec_expr("-x + 1"), Some(expected));
    }

    #[test]
    fn parses_boolean_literals() {
        assert_eq!(parse_spec_expr("true"), Some(Formula::Bool(true)));
        assert_eq!(parse_spec_expr("false"), Some(Formula::Bool(false)));
    }

    #[test]
    fn rejects_invalid_inputs() {
        for input in ["", "x >", "old(x", "old(x + 1)", "a < b < c", "()", "x @ 1"] {
            assert_eq!(parse_spec_expr(input), None, "input should fail: {input}");
        }
    }

    // === Result API tests ===

    #[test]
    fn test_result_api_empty_input() {
        let err = parse_spec_expr_result("").unwrap_err();
        assert!(matches!(err, SpecParseError::Empty));

        let err = parse_spec_expr_result("   ").unwrap_err();
        assert!(matches!(err, SpecParseError::Empty));
    }

    #[test]
    fn test_result_api_unexpected_char() {
        let err = parse_spec_expr_result("x @ 1").unwrap_err();
        match err {
            SpecParseError::UnexpectedChar { ch, position } => {
                assert_eq!(ch, '@');
                assert_eq!(position, 2);
            }
            other => panic!("expected UnexpectedChar, got {other:?}"),
        }
    }

    #[test]
    fn test_result_api_trailing_tokens() {
        let err = parse_spec_expr_result("a < b < c").unwrap_err();
        assert!(matches!(err, SpecParseError::TrailingTokens));
    }

    #[test]
    fn test_result_api_success() {
        let formula = parse_spec_expr_result("x > 0").expect("should parse");
        assert!(matches!(formula, Formula::Gt(..)));
    }

    // === Quantifier tests ===

    #[test]
    fn test_forall_basic() {
        let formula = parse_spec_expr_result("forall(i, 0..n, i >= 0)").expect("should parse");
        match formula {
            Formula::Forall(bindings, body) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "i");
                // body should be Implies(range_guard, i >= 0)
                assert!(matches!(*body, Formula::Implies(..)));
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn test_exists_basic() {
        let formula = parse_spec_expr_result("exists(j, 0..n, j == k)").expect("should parse");
        match formula {
            Formula::Exists(bindings, body) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "j");
                // body should be And([range_guard, j == k])
                assert!(matches!(*body, Formula::And(..)));
            }
            other => panic!("expected Exists, got {other:?}"),
        }
    }

    #[test]
    fn test_native_typed_forall_multiple_binders() {
        let formula = parse_spec_expr_result("forall i j: usize, i < j => balance == balance")
            .expect("native typed quantifier should parse");
        let Formula::Forall(bindings, body) = formula else {
            panic!("expected Forall");
        };
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0], ("i".into(), Sort::Int));
        // `usize`'s target-independent universal interpretation is guarded as
        // non-negative, then the nested `j` binder and authored implication
        // remain inside it. Grouped source binders canonicalize to nested
        // one-binding nodes to match the public high-level AST exactly.
        let Formula::Implies(_, inner) = *body else { panic!("expected outer usize domain guard") };
        let Formula::Forall(inner_bindings, _) = *inner else { panic!("expected nested j forall") };
        assert_eq!(inner_bindings, vec![("j".into(), Sort::Int)]);
    }

    #[test]
    fn test_primed_names_fail_closed_without_post_state_bindings() {
        for input in ["balance' == balance", "x'' == x", "forall i: u8, x' == i"] {
            let err = parse_spec_expr_result(input).unwrap_err();
            assert!(
                matches!(err, SpecParseError::UnexpectedChar { ch: '\'', .. }),
                "primed name must be rejected in `{input}`, got {err:?}"
            );
        }
    }

    #[test]
    fn test_native_typed_exists_fixed_width_has_exact_domain() {
        let formula = parse_spec_expr_result("exists i: u8, i == 7").expect("should parse");
        let Formula::Exists(bindings, body) = formula else {
            panic!("expected Exists");
        };
        assert_eq!(bindings, vec![("i".into(), Sort::Int)]);
        assert!(matches!(*body, Formula::And(..)));
    }

    #[test]
    fn test_target_independent_exists_usize_fails_closed() {
        let err = parse_spec_expr_result("exists i: usize, i == i").unwrap_err();
        assert!(matches!(err, SpecParseError::InvalidQuantifier { .. }), "got {err:?}");
    }

    #[test]
    fn test_native_bool_binder_preserves_bool_sort() {
        let formula = parse_spec_expr_result("forall flag: bool, flag => flag")
            .expect("bool binder should parse");
        let Formula::Forall(bindings, body) = formula else {
            panic!("expected Forall");
        };
        assert_eq!(bindings, vec![("flag".into(), Sort::Bool)]);
        let Formula::Implies(lhs, rhs) = *body else {
            panic!("expected implication body");
        };
        assert_eq!(*lhs, Formula::Var("flag".into(), Sort::Bool));
        assert_eq!(*rhs, Formula::Var("flag".into(), Sort::Bool));
    }

    #[test]
    fn test_forall_with_complex_body() {
        let formula =
            parse_spec_expr_result("forall(i, 0..n, arr > 0 && arr < 100)").expect("should parse");
        assert!(matches!(formula, Formula::Forall(..)));
    }

    #[test]
    fn test_quantifier_missing_comma() {
        let err = parse_spec_expr_result("forall(i 0..n, true)").unwrap_err();
        assert!(matches!(err, SpecParseError::UnexpectedToken { .. }), "got {err:?}");
    }

    #[test]
    fn test_quantifier_missing_range() {
        let err = parse_spec_expr_result("forall(i, 0, true)").unwrap_err();
        assert!(matches!(err, SpecParseError::InvalidQuantifier { .. }), "got {err:?}");
    }

    #[test]
    fn test_quantifier_keywords_not_called_are_reserved() {
        assert!(parse_spec_expr_result("forall + 1").is_err());
        assert!(parse_spec_expr_result("exists + 1").is_err());
    }

    // === Dot-access tests ===

    #[test]
    fn test_dot_len() {
        let formula = parse_spec_expr_result("arr.len() > 0").expect("should parse");
        match formula {
            Formula::Gt(lhs, rhs) => {
                assert_eq!(*lhs, var("arr_len"));
                assert_eq!(*rhs, int(0));
            }
            other => panic!("expected Gt, got {other:?}"),
        }
    }

    #[test]
    fn test_dot_is_empty() {
        let formula = parse_spec_expr_result("s.is_empty()").expect("should parse");
        match formula {
            Formula::Eq(lhs, rhs) => {
                assert_eq!(*lhs, var("s_len"));
                assert_eq!(*rhs, int(0));
            }
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_dot_len_in_comparison() {
        let formula = parse_spec_expr_result("arr.len() > i").expect("should parse");
        assert!(matches!(formula, Formula::Gt(..)));
    }

    #[test]
    fn test_unsupported_method() {
        let err = parse_spec_expr_result("x.foo()").unwrap_err();
        assert!(matches!(err, SpecParseError::UnsupportedMethod { .. }));
    }

    // === Complex expression tests ===

    #[test]
    fn test_nested_quantifier_in_conjunction() {
        let formula =
            parse_spec_expr_result("n > 0 && forall(i, 0..n, i >= 0)").expect("should parse");
        assert!(matches!(formula, Formula::And(..)));
    }

    #[test]
    fn test_result_equals_sum() {
        let formula = parse_spec_expr_result("result == a + b").expect("should parse");
        match formula {
            Formula::Eq(lhs, rhs) => {
                assert_eq!(*lhs, var("_0"));
                assert!(matches!(*rhs, Formula::Add(..)));
            }
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_prefix_deref_of_reference_param() {
        // `#[requires(*a <= 100)]` where `a: &u32`. The compiler emits the deref
        // verbatim; the body names the referent `"a*"` (suffix `*`), so the spec
        // must too. Regression for over-refutation audit defect #4.
        let formula = parse_spec_expr("*a <= 100").expect("prefix deref should parse");
        match formula {
            Formula::Le(lhs, rhs) => {
                assert_eq!(*lhs, var("a*"));
                assert_eq!(*rhs, int(100));
            }
            other => panic!("expected Le(a*, 100), got {other:?}"),
        }
    }

    #[test]
    fn test_prefix_deref_does_not_break_infix_multiply() {
        // A leading `*` is a deref; an infix `*` between operands stays multiply.
        // `a * b` must remain `Mul(a, b)`, and `*a * b` must be `Mul(a*, b)`.
        let mul = parse_spec_expr("a * b").expect("multiply should parse");
        assert!(matches!(mul, Formula::Mul(..)), "a * b must stay Mul, got {mul:?}");

        let deref_mul = parse_spec_expr("*a * b").expect("deref-then-multiply should parse");
        match deref_mul {
            Formula::Mul(lhs, rhs) => {
                assert_eq!(*lhs, var("a*"));
                assert_eq!(*rhs, var("b"));
            }
            other => panic!("expected Mul(a*, b), got {other:?}"),
        }
    }

    #[test]
    fn test_prefix_deref_in_conjunction() {
        // `*a <= 100 && *b >= 1` — both derefs lower to suffix-`*` names.
        let formula = parse_spec_expr("*a <= 100 && *b >= 1").expect("should parse");
        match formula {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                assert!(matches!(&clauses[0], Formula::Le(l, _) if **l == var("a*")));
                assert!(matches!(&clauses[1], Formula::Ge(l, _) if **l == var("b*")));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_tuple_field_projection_on_result() {
        // `#[ensures(|ret| ret.0 == ret.1)]` — the compiler lowers the binding to
        // `result` (mapped to `_0`); numeric fields append `.i`, matching the MIR
        // `Field(i)` naming (`_0.0`, `_0.1`). Regression for audit defect #2.
        let formula = parse_spec_expr("result.0 == result.1").expect("tuple fields should parse");
        match formula {
            Formula::Eq(lhs, rhs) => {
                assert_eq!(*lhs, var("_0.0"));
                assert_eq!(*rhs, var("_0.1"));
            }
            other => panic!("expected Eq(_0.0, _0.1), got {other:?}"),
        }
    }

    #[test]
    fn test_tuple_field_projection_in_arithmetic() {
        // `p.0 + p.1` — a tuple index inside an arithmetic expression.
        let formula = parse_spec_expr("p.0 + p.1 == 10").expect("should parse");
        match formula {
            Formula::Eq(lhs, rhs) => {
                assert!(matches!(*lhs, Formula::Add(..)), "lhs should be Add, got {lhs:?}");
                assert_eq!(*rhs, int(10));
            }
            other => panic!("expected Eq(Add, 10), got {other:?}"),
        }
    }

    #[test]
    fn test_complex_spec_with_implication_and_quantifier() {
        let formula =
            parse_spec_expr_result("n > 0 => forall(i, 0..n, i >= 0)").expect("should parse");
        assert!(matches!(formula, Formula::Implies(..)));
    }

    #[test]
    fn test_error_display_messages() {
        let cases = vec![
            (SpecParseError::Empty, "empty spec expression"),
            (
                SpecParseError::UnexpectedChar { ch: '#', position: 3 },
                "unexpected character '#' at position 3",
            ),
            (SpecParseError::TrailingTokens, "trailing tokens after expression"),
            (
                SpecParseError::InvalidQuantifier { detail: "bad range".into() },
                "invalid quantifier syntax: bad range",
            ),
            (
                SpecParseError::UnsupportedMethod { method: "foo".into() },
                "unsupported method call: foo",
            ),
        ];

        for (err, expected_msg) in cases {
            assert_eq!(err.to_string(), expected_msg);
        }
    }

    // === Trust SAFE_API §3: uninterpreted predicate (Formula::Pred) parsing ===

    fn pred(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Pred(crate::Symbol::intern(name), args)
    }

    #[test]
    fn parses_unary_pred() {
        assert_eq!(parse_spec_expr("dir_open(dir)"), Some(pred("dir_open", vec![var("dir")])));
    }

    #[test]
    fn parses_zero_arity_pred() {
        assert_eq!(parse_spec_expr("priv_dropped()"), Some(pred("priv_dropped", vec![])));
    }

    #[test]
    fn parses_pred_conjunction() {
        let expected = Formula::And(vec![
            pred("dir_open", vec![var("dir")]),
            pred("single_component", vec![var("name")]),
        ]);
        assert_eq!(parse_spec_expr("dir_open(dir) && single_component(name)"), Some(expected));
    }

    #[test]
    fn accessor_lowers_to_same_handle_keyed_var() {
        // `dir.fd()` and bare `dir` must produce the identical Pred argument.
        assert_eq!(parse_spec_expr("dir_open(dir.fd())"), parse_spec_expr("dir_open(dir)"));
        assert_eq!(
            parse_spec_expr("single_component(name.components())"),
            Some(pred("single_component", vec![var("name")]))
        );
    }

    #[test]
    fn rejects_out_of_vocabulary_predicate() {
        // Not in PRED_VOCAB -> not routed to Pred; the trailing `(` fails the
        // parse (today's behavior), never a silent attacker-defined predicate.
        assert_eq!(parse_spec_expr("attacker_predicate(x)"), None);
        assert_eq!(parse_spec_expr("foo(x)"), None);
    }

    #[test]
    fn rejects_wrong_arity_predicate() {
        // Known name, wrong arity -> hard parse error (never a silent accept).
        assert!(parse_spec_expr_result("dir_open(a, b)").is_err());
        assert_eq!(parse_spec_expr("dir_open(a, b)"), None);
        // Zero args for an arity-1 predicate.
        assert_eq!(parse_spec_expr("dir_open()"), None);
    }

    #[test]
    fn bare_vocabulary_name_without_parens_is_reserved() {
        // Predicate symbols occupy a closed namespace. A bare occurrence must
        // not become a source Var that aliases the same solver symbol.
        assert_eq!(parse_spec_expr("priv_dropped"), None);
    }

    #[test]
    fn pred_argument_gets_its_declared_sort() {
        let Some(Formula::Pred(_, args)) = parse_spec_expr("dir_open(dir)") else {
            panic!("expected a Pred");
        };
        let Formula::Var(_, sort) = &args[0] else {
            panic!("expected a Var argument");
        };
        assert_eq!(*sort, pred_arg_sorts("dir_open").unwrap()[0]);
    }

    // === Gap-A: CHECKER-CORE recursive-spec predicates (`is_whnf`, ...) ===
    //
    // The STATE rung: a `#[ensures]` can now state a checker-core structural
    // property of a literal clean-kernel function's RESULT. `result` maps to the
    // return slot `_0` (via `map_var_name`), so `is_whnf(result)` becomes the VC
    // vocabulary `Pred("is_whnf", [_0])`. The predicate is opaque + fail-closed
    // (SMT can never prove it), its recursive meaning bound to clean-verify's
    // inductive `is_whnf` by the semantics registry.

    #[test]
    fn parses_checker_core_is_whnf_on_result() {
        // The flagship recursive-spec postcondition: the returned expression is in
        // weak-head normal form. `result` -> `_0` (the return slot the vcgen
        // postcondition lane pins), so this is exactly what a `#[ensures(move |r|
        // is_whnf(r))]` on an `Expr`-returning kernel fn lowers to.
        assert_eq!(parse_spec_expr("is_whnf(result)"), Some(pred("is_whnf", vec![var("_0")])));
    }

    #[test]
    fn checker_core_pred_is_distinct_from_safety_pred() {
        // Same opaque, fail-closed `Formula::Pred` lowering, but a DISTINCT category
        // (checker-core structural, not safety-capability).
        assert!(crate::is_checker_core_pred("is_whnf"));
        assert!(!crate::is_checker_core_pred("dir_open"));
        // The recursive semantics binding is present and non-dangling: it names a
        // real clean-verify inductive definition + a DerivedProved backing lemma.
        let sem = crate::checker_core_semantics("is_whnf").expect("is_whnf must be registered");
        assert_eq!(sem.clean_verify_def, "is_whnf");
        assert_eq!(sem.backing_lemma, "value_is_whnf");
        // A predicate with no registry entry has no sanctioned discharge (fail-closed).
        assert!(crate::checker_core_semantics("dir_open").is_none());
    }

    #[test]
    fn checker_core_pred_conjoins_with_safety_pred() {
        // Both vocabularies coexist in one spec expression via the union accessor.
        let expected = Formula::And(vec![
            pred("is_whnf", vec![var("_0")]),
            pred("dir_open", vec![var("dir")]),
        ]);
        assert_eq!(parse_spec_expr("is_whnf(result) && dir_open(dir)"), Some(expected));
    }

    #[test]
    fn rejects_wrong_arity_checker_core_predicate() {
        // NEGATIVE CONTROL: a known checker-core name with the wrong arity is a HARD
        // parse error, never a silent accept.
        assert!(parse_spec_expr_result("is_whnf()").is_err());
        assert_eq!(parse_spec_expr("is_whnf()"), None);
        assert_eq!(parse_spec_expr("is_whnf(a, b)"), None);
    }

    #[test]
    fn rejects_out_of_vocabulary_checker_core_lookalike() {
        // NEGATIVE CONTROL: a plausible-but-unregistered checker-core name is NOT a
        // Pred (the trailing `(` fails the parse) — never a silent, unbacked
        // structural predicate.
        assert_eq!(parse_spec_expr("is_normal_form(result)"), None);
        assert_eq!(parse_spec_expr("no_free_var_below(result, k)"), None);
    }

    #[test]
    fn parses_fixed_width_primitive_integer_constants() {
        assert_eq!(
            parse_spec_expr("a <= u32::MAX - b"),
            Some(Formula::Le(
                Box::new(var("a")),
                Box::new(Formula::Sub(
                    Box::new(Formula::Int(u32::MAX as i128)),
                    Box::new(var("b")),
                )),
            ))
        );
        assert_eq!(
            parse_spec_expr("x == i128::MIN"),
            Some(Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(i128::MIN)),))
        );
        assert_eq!(
            parse_spec_expr("x == u128::MAX"),
            Some(Formula::Eq(Box::new(var("x")), Box::new(Formula::UInt(u128::MAX)),))
        );
    }

    #[test]
    fn rejects_target_dependent_or_unknown_associated_constants() {
        assert!(parse_spec_expr_result("x < usize::MAX").is_err());
        assert!(parse_spec_expr_result("x < u32::BOGUS").is_err());
        assert!(parse_spec_expr_result("x < attacker::MAX").is_err());
    }

    #[test]
    fn consecutive_numeric_field_segments_parse_as_nested_fields() {
        // `(*self).0.0` — the canonicalized spelling of a nested-struct bound
        // (`self.min.x` on `&self`). Before round-13 the tokenizer lexed the
        // second `0.0` as a FLOAT literal and every Aabb/Transform contract
        // died as SpecUnverifiable.
        let f = parse_spec_expr("self.0.0").expect("nested numeric fields parse");
        assert_eq!(f, Formula::Var("self.0.0".into(), Sort::Int));
        let f = parse_spec_expr("((*self).0.0) <= (1.0e149)").expect("deref chain parses");
        let Formula::Le(lhs, _) = f else { panic!("expected Le, got {f:?}") };
        assert_eq!(
            *lhs,
            Formula::Var("self*.0.0".into(), Sort::Float { eb: 11, sb: 53 }),
            "the chain var must be float-coerced by the comparison"
        );
        // Float literals in VALUE position are untouched (the context check is
        // the preceding Dot token, which a parenthesized literal never has).
        assert!(parse_spec_expr("x <= 0.5").is_some());
        // A range keeps its integer + DotDot shape.
        assert!(parse_spec_expr("forall(i, 0..4, i >= 0)").is_some());
    }
}
