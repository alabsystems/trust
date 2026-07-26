// trust-temporal/ltl.rs: Linear Temporal Logic formula representation and parsing
//
// Provides an LTL formula AST, a simple recursive descent parser, negation,
// and positive normal form (PNF) conversion. PNF pushes negations to atoms,
// which is required for Buchi automata construction in liveness checking.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

/// A Linear Temporal Logic formula.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LtlFormula {
    /// Atomic proposition: a named boolean predicate over states.
    Atomic(String),
    /// Logical negation: !phi.
    Not(Box<LtlFormula>),
    /// Conjunction: phi /\ psi.
    And(Box<LtlFormula>, Box<LtlFormula>),
    /// Disjunction: phi \/ psi.
    Or(Box<LtlFormula>, Box<LtlFormula>),
    /// Next: X phi (phi holds in the next state).
    Next(Box<LtlFormula>),
    /// Until: phi U psi (phi holds until psi becomes true).
    Until(Box<LtlFormula>, Box<LtlFormula>),
    /// Eventually: F phi (equivalent to true U phi).
    Eventually(Box<LtlFormula>),
    /// Always: G phi (equivalent to !F !phi).
    Always(Box<LtlFormula>),
    /// Implication: phi -> psi (sugar for !phi \/ psi).
    Implies(Box<LtlFormula>, Box<LtlFormula>),
}

/// Errors from LTL formula parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParseError {
    /// Unexpected end of input.
    UnexpectedEof,
    /// Unexpected token at the given position.
    UnexpectedToken { pos: usize, found: String },
    /// Unmatched parenthesis.
    UnmatchedParen { pos: usize },
    /// Empty formula.
    EmptyFormula,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::UnexpectedEof => write!(f, "unexpected end of input"),
            ParseError::UnexpectedToken { pos, found } => {
                write!(f, "unexpected token '{found}' at position {pos}")
            }
            ParseError::UnmatchedParen { pos } => {
                write!(f, "unmatched parenthesis at position {pos}")
            }
            ParseError::EmptyFormula => write!(f, "empty formula"),
        }
    }
}

impl std::error::Error for ParseError {}

impl fmt::Display for LtlFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LtlFormula::Atomic(name) => write!(f, "{name}"),
            LtlFormula::Not(inner) => write!(f, "!({inner})"),
            LtlFormula::And(l, r) => write!(f, "({l} && {r})"),
            LtlFormula::Or(l, r) => write!(f, "({l} || {r})"),
            LtlFormula::Next(inner) => write!(f, "X({inner})"),
            LtlFormula::Until(l, r) => write!(f, "({l} U {r})"),
            LtlFormula::Eventually(inner) => write!(f, "F({inner})"),
            LtlFormula::Always(inner) => write!(f, "G({inner})"),
            LtlFormula::Implies(l, r) => write!(f, "({l} -> {r})"),
        }
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Token types produced by the lexer.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Ident(String),
    Not,
    And,
    Or,
    Implies,
    Next,       // X
    Until,      // U
    Eventually, // F
    Always,     // G
    LParen,
    RParen,
}

/// Tokenize an LTL formula string.
fn tokenize(input: &str) -> Result<Vec<(Token, usize)>, ParseError> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        match chars[i] {
            ' ' | '\t' | '\n' | '\r' => {
                i += 1;
            }
            '(' => {
                tokens.push((Token::LParen, i));
                i += 1;
            }
            ')' => {
                tokens.push((Token::RParen, i));
                i += 1;
            }
            '!' => {
                tokens.push((Token::Not, i));
                i += 1;
            }
            '&' if i + 1 < chars.len() && chars[i + 1] == '&' => {
                tokens.push((Token::And, i));
                i += 2;
            }
            '|' if i + 1 < chars.len() && chars[i + 1] == '|' => {
                tokens.push((Token::Or, i));
                i += 2;
            }
            '-' if i + 1 < chars.len() && chars[i + 1] == '>' => {
                tokens.push((Token::Implies, i));
                i += 2;
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let start = i;
                while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let word: String = chars[start..i].iter().collect();
                let tok = match word.as_str() {
                    "X" => Token::Next,
                    "U" => Token::Until,
                    "F" => Token::Eventually,
                    "G" => Token::Always,
                    _ => Token::Ident(word),
                };
                tokens.push((tok, start));
            }
            _ => {
                return Err(ParseError::UnexpectedToken { pos: i, found: chars[i].to_string() });
            }
        }
    }

    Ok(tokens)
}

/// Recursive descent parser for LTL formulas.
///
/// Grammar (informal):
/// ```text
/// formula     = implication
/// implication = disjunction ("->" implication)?
/// disjunction = conjunction ("||" conjunction)*
/// conjunction = unary ("&&" unary)*
/// unary       = "!" unary | "X" unary | "F" unary | "G" unary | primary ("U" unary)?
/// primary     = IDENT | "(" formula ")"
/// ```
struct Parser {
    tokens: Vec<(Token, usize)>,
    pos: usize,
}

impl Parser {
    fn new(tokens: Vec<(Token, usize)>) -> Self {
        Self { tokens, pos: 0 }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos).map(|(t, _)| t)
    }

    fn peek_pos(&self) -> usize {
        self.tokens.get(self.pos).map_or(0, |(_, p)| *p)
    }

    fn advance(&mut self) -> Option<(Token, usize)> {
        if self.pos < self.tokens.len() {
            let tok = self.tokens[self.pos].clone();
            self.pos += 1;
            Some(tok)
        } else {
            None
        }
    }

    fn parse_formula(&mut self) -> Result<LtlFormula, ParseError> {
        self.parse_implication()
    }

    fn parse_implication(&mut self) -> Result<LtlFormula, ParseError> {
        let left = self.parse_disjunction()?;
        if self.peek() == Some(&Token::Implies) {
            self.advance();
            let right = self.parse_implication()?;
            Ok(LtlFormula::Implies(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn parse_disjunction(&mut self) -> Result<LtlFormula, ParseError> {
        let mut left = self.parse_conjunction()?;
        while self.peek() == Some(&Token::Or) {
            self.advance();
            let right = self.parse_conjunction()?;
            left = LtlFormula::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_conjunction(&mut self) -> Result<LtlFormula, ParseError> {
        let mut left = self.parse_unary()?;
        while self.peek() == Some(&Token::And) {
            self.advance();
            let right = self.parse_unary()?;
            left = LtlFormula::And(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<LtlFormula, ParseError> {
        match self.peek() {
            Some(Token::Not) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(LtlFormula::Not(Box::new(inner)))
            }
            Some(Token::Next) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(LtlFormula::Next(Box::new(inner)))
            }
            Some(Token::Eventually) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(LtlFormula::Eventually(Box::new(inner)))
            }
            Some(Token::Always) => {
                self.advance();
                let inner = self.parse_unary()?;
                Ok(LtlFormula::Always(Box::new(inner)))
            }
            _ => {
                let primary = self.parse_primary()?;
                // Check for infix Until
                if self.peek() == Some(&Token::Until) {
                    self.advance();
                    let right = self.parse_unary()?;
                    Ok(LtlFormula::Until(Box::new(primary), Box::new(right)))
                } else {
                    Ok(primary)
                }
            }
        }
    }

    fn parse_primary(&mut self) -> Result<LtlFormula, ParseError> {
        match self.peek().cloned() {
            Some(Token::Ident(name)) => {
                self.advance();
                Ok(LtlFormula::Atomic(name))
            }
            Some(Token::LParen) => {
                let paren_pos = self.peek_pos();
                self.advance();
                let inner = self.parse_formula()?;
                if self.peek() != Some(&Token::RParen) {
                    return Err(ParseError::UnmatchedParen { pos: paren_pos });
                }
                self.advance();
                Ok(inner)
            }
            Some(_) => {
                let pos = self.peek_pos();
                let (tok, _) = self.advance().expect("invariant: peeked Some");
                Err(ParseError::UnexpectedToken { pos, found: format!("{tok:?}") })
            }
            None => Err(ParseError::UnexpectedEof),
        }
    }
}

/// Parse an LTL formula string into an `LtlFormula` AST.
///
/// Supported syntax:
/// - Atoms: identifiers like `p`, `ready`, `at_goal`
/// - Boolean: `!` (not), `&&` (and), `||` (or), `->` (implies)
/// - Temporal: `X` (next), `F` (eventually), `G` (always), `U` (until, infix)
/// - Parentheses for grouping
///
/// # Errors
///
/// Returns `ParseError` on malformed input.
pub fn parse_ltl(input: &str) -> Result<LtlFormula, ParseError> {
    let input = input.trim();
    if input.is_empty() {
        return Err(ParseError::EmptyFormula);
    }
    let tokens = tokenize(input)?;
    if tokens.is_empty() {
        return Err(ParseError::EmptyFormula);
    }
    let mut parser = Parser::new(tokens);
    let formula = parser.parse_formula()?;
    if parser.pos < parser.tokens.len() {
        let pos = parser.peek_pos();
        return Err(ParseError::UnexpectedToken {
            pos,
            found: format!("{:?}", parser.tokens[parser.pos].0),
        });
    }
    Ok(formula)
}

// ---------------------------------------------------------------------------
// Negation and positive normal form
// ---------------------------------------------------------------------------

/// Negate an LTL formula: wraps it in `Not`.
#[must_use]
pub fn negate(formula: &LtlFormula) -> LtlFormula {
    LtlFormula::Not(Box::new(formula.clone()))
}

/// Convert an LTL formula to Positive Normal Form (PNF).
///
/// In PNF, negation only appears directly before atomic propositions.
/// This is done by pushing `Not` inward using dualities:
/// - `!!phi` => `phi`
/// - `!(phi && psi)` => `!phi || !psi`
/// - `!(phi || psi)` => `!phi && !psi`
/// - `!X phi` => `X !phi`
/// - `!F phi` => `G !phi`
/// - `!G phi` => `F !phi`
/// - `!(phi U psi)` => `(!psi) U (!phi && !psi) || G(!psi)`
///   Simplified: we use the Release operator semantics but express via Until/Always.
///   Actually: `!(phi U psi)` = `(!psi) R (!phi)` where R is "release".
///   Since we don't have Release, we express it as: `G(!psi) || (!psi U (!phi && !psi))`
/// - `!(phi -> psi)` => `phi && !psi`
#[cfg(test)]
#[must_use]
fn to_positive_normal_form(formula: &LtlFormula) -> LtlFormula {
    match formula {
        LtlFormula::Atomic(_) => formula.clone(),

        LtlFormula::Not(inner) => push_negation(inner),

        LtlFormula::And(l, r) => LtlFormula::And(
            Box::new(to_positive_normal_form(l)),
            Box::new(to_positive_normal_form(r)),
        ),

        LtlFormula::Or(l, r) => LtlFormula::Or(
            Box::new(to_positive_normal_form(l)),
            Box::new(to_positive_normal_form(r)),
        ),

        LtlFormula::Next(inner) => LtlFormula::Next(Box::new(to_positive_normal_form(inner))),

        LtlFormula::Until(l, r) => LtlFormula::Until(
            Box::new(to_positive_normal_form(l)),
            Box::new(to_positive_normal_form(r)),
        ),

        LtlFormula::Eventually(inner) => {
            LtlFormula::Eventually(Box::new(to_positive_normal_form(inner)))
        }

        LtlFormula::Always(inner) => LtlFormula::Always(Box::new(to_positive_normal_form(inner))),

        LtlFormula::Implies(l, r) => {
            // phi -> psi  =  !phi || psi
            to_positive_normal_form(&LtlFormula::Or(
                Box::new(LtlFormula::Not(l.clone())),
                r.clone(),
            ))
        }
    }
}

/// Push a negation inward (helper for PNF conversion).
#[cfg(test)]
fn push_negation(inner: &LtlFormula) -> LtlFormula {
    match inner {
        // !!phi => phi
        LtlFormula::Not(phi) => to_positive_normal_form(phi),

        // !atom => Not(atom) (already in PNF)
        LtlFormula::Atomic(_) => LtlFormula::Not(Box::new(inner.clone())),

        // !(phi && psi) => !phi || !psi
        LtlFormula::And(l, r) => {
            LtlFormula::Or(Box::new(push_negation(l)), Box::new(push_negation(r)))
        }

        // !(phi || psi) => !phi && !psi
        LtlFormula::Or(l, r) => {
            LtlFormula::And(Box::new(push_negation(l)), Box::new(push_negation(r)))
        }

        // !X phi => X !phi
        LtlFormula::Next(phi) => LtlFormula::Next(Box::new(push_negation(phi))),

        // !F phi => G !phi
        LtlFormula::Eventually(phi) => LtlFormula::Always(Box::new(push_negation(phi))),

        // !G phi => F !phi
        LtlFormula::Always(phi) => LtlFormula::Eventually(Box::new(push_negation(phi))),

        // !(phi U psi) => G(!psi) || (!psi U (!phi && !psi))
        LtlFormula::Until(l, r) => {
            let neg_r = push_negation(r);
            let neg_l = push_negation(l);
            LtlFormula::Or(
                Box::new(LtlFormula::Always(Box::new(neg_r.clone()))),
                Box::new(LtlFormula::Until(
                    Box::new(neg_r),
                    Box::new(LtlFormula::And(Box::new(neg_l), Box::new(push_negation(r)))),
                )),
            )
        }

        // !(phi -> psi) => phi && !psi
        LtlFormula::Implies(l, r) => {
            LtlFormula::And(Box::new(to_positive_normal_form(l)), Box::new(push_negation(r)))
        }
    }
}

/// Check whether a formula is in positive normal form (negation only on atoms).
#[cfg(test)]
#[must_use]
fn is_positive_normal_form(formula: &LtlFormula) -> bool {
    match formula {
        LtlFormula::Atomic(_) => true,
        LtlFormula::Not(inner) => matches!(inner.as_ref(), LtlFormula::Atomic(_)),
        LtlFormula::And(l, r) | LtlFormula::Or(l, r) | LtlFormula::Until(l, r) => {
            is_positive_normal_form(l) && is_positive_normal_form(r)
        }
        LtlFormula::Next(inner) | LtlFormula::Eventually(inner) | LtlFormula::Always(inner) => {
            is_positive_normal_form(inner)
        }
        LtlFormula::Implies(_, _) => false, // Implies is sugar, not PNF
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- parse_ltl ----

    #[test]
    fn test_parse_ltl_atomic() {
        let f = parse_ltl("ready").unwrap();
        assert_eq!(f, LtlFormula::Atomic("ready".into()));
    }

    #[test]
    fn test_parse_ltl_eventually() {
        let f = parse_ltl("F done").unwrap();
        assert_eq!(f, LtlFormula::Eventually(Box::new(LtlFormula::Atomic("done".into()))));
    }

    #[test]
    fn test_parse_ltl_always() {
        let f = parse_ltl("G safe").unwrap();
        assert_eq!(f, LtlFormula::Always(Box::new(LtlFormula::Atomic("safe".into()))));
    }

    #[test]
    fn test_parse_ltl_next() {
        let f = parse_ltl("X running").unwrap();
        assert_eq!(f, LtlFormula::Next(Box::new(LtlFormula::Atomic("running".into()))));
    }

    #[test]
    fn test_parse_ltl_until() {
        let f = parse_ltl("waiting U served").unwrap();
        assert_eq!(
            f,
            LtlFormula::Until(
                Box::new(LtlFormula::Atomic("waiting".into())),
                Box::new(LtlFormula::Atomic("served".into())),
            )
        );
    }

    #[test]
    fn test_parse_ltl_negation() {
        let f = parse_ltl("!error").unwrap();
        assert_eq!(f, LtlFormula::Not(Box::new(LtlFormula::Atomic("error".into()))));
    }

    #[test]
    fn test_parse_ltl_conjunction() {
        let f = parse_ltl("p && q").unwrap();
        assert_eq!(
            f,
            LtlFormula::And(
                Box::new(LtlFormula::Atomic("p".into())),
                Box::new(LtlFormula::Atomic("q".into())),
            )
        );
    }

    #[test]
    fn test_parse_ltl_disjunction() {
        let f = parse_ltl("p || q").unwrap();
        assert_eq!(
            f,
            LtlFormula::Or(
                Box::new(LtlFormula::Atomic("p".into())),
                Box::new(LtlFormula::Atomic("q".into())),
            )
        );
    }

    #[test]
    fn test_parse_ltl_implies() {
        let f = parse_ltl("request -> F response").unwrap();
        assert_eq!(
            f,
            LtlFormula::Implies(
                Box::new(LtlFormula::Atomic("request".into())),
                Box::new(LtlFormula::Eventually(Box::new(LtlFormula::Atomic("response".into())))),
            )
        );
    }

    #[test]
    fn test_parse_ltl_parentheses() {
        let f = parse_ltl("G (p || q)").unwrap();
        assert_eq!(
            f,
            LtlFormula::Always(Box::new(LtlFormula::Or(
                Box::new(LtlFormula::Atomic("p".into())),
                Box::new(LtlFormula::Atomic("q".into())),
            )))
        );
    }

    #[test]
    fn test_parse_ltl_nested_temporal() {
        let f = parse_ltl("G F alive").unwrap();
        assert_eq!(
            f,
            LtlFormula::Always(Box::new(LtlFormula::Eventually(Box::new(LtlFormula::Atomic(
                "alive".into()
            )))))
        );
    }

    #[test]
    fn test_parse_ltl_empty_returns_error() {
        assert_eq!(parse_ltl("").unwrap_err(), ParseError::EmptyFormula);
        assert_eq!(parse_ltl("   ").unwrap_err(), ParseError::EmptyFormula);
    }

    #[test]
    fn test_parse_ltl_unmatched_paren() {
        let err = parse_ltl("(p && q").unwrap_err();
        assert!(matches!(err, ParseError::UnmatchedParen { .. }));
    }

    #[test]
    fn test_parse_ltl_unexpected_token() {
        let err = parse_ltl("@bad").unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedToken { .. }));
    }

    // ---- negate ----

    #[test]
    fn test_negate_wraps_in_not() {
        let f = LtlFormula::Atomic("p".into());
        let neg = negate(&f);
        assert_eq!(neg, LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into()))));
    }

    #[test]
    fn test_negate_double_negation() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into())));
        let neg = negate(&f);
        assert_eq!(
            neg,
            LtlFormula::Not(Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into())))))
        );
    }

    // ---- to_positive_normal_form ----

    #[test]
    fn test_pnf_double_negation_eliminated() {
        let f = parse_ltl("!!p").unwrap();
        let pnf = to_positive_normal_form(&f);
        assert_eq!(pnf, LtlFormula::Atomic("p".into()));
        assert!(is_positive_normal_form(&pnf));
    }

    #[test]
    fn test_pnf_de_morgan_and() {
        // !(p && q) => !p || !q
        let f = parse_ltl("!(p && q)").unwrap();
        let pnf = to_positive_normal_form(&f);
        assert_eq!(
            pnf,
            LtlFormula::Or(
                Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into())))),
                Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic("q".into())))),
            )
        );
        assert!(is_positive_normal_form(&pnf));
    }

    #[test]
    fn test_pnf_de_morgan_or() {
        // !(p || q) => !p && !q
        let f = parse_ltl("!(p || q)").unwrap();
        let pnf = to_positive_normal_form(&f);
        assert_eq!(
            pnf,
            LtlFormula::And(
                Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into())))),
                Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic("q".into())))),
            )
        );
        assert!(is_positive_normal_form(&pnf));
    }

    #[test]
    fn test_pnf_negated_eventually_becomes_always() {
        // !F p => G !p
        let f = parse_ltl("!F p").unwrap();
        let pnf = to_positive_normal_form(&f);
        assert_eq!(
            pnf,
            LtlFormula::Always(Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into())))))
        );
        assert!(is_positive_normal_form(&pnf));
    }

    #[test]
    fn test_pnf_negated_always_becomes_eventually() {
        // !G p => F !p
        let f = parse_ltl("!G p").unwrap();
        let pnf = to_positive_normal_form(&f);
        assert_eq!(
            pnf,
            LtlFormula::Eventually(Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic(
                "p".into()
            )))))
        );
        assert!(is_positive_normal_form(&pnf));
    }

    #[test]
    fn test_pnf_negated_next() {
        // !X p => X !p
        let f = parse_ltl("!X p").unwrap();
        let pnf = to_positive_normal_form(&f);
        assert_eq!(
            pnf,
            LtlFormula::Next(Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into())))))
        );
        assert!(is_positive_normal_form(&pnf));
    }

    #[test]
    fn test_pnf_implies_desugared() {
        // p -> q => !p || q
        let f = parse_ltl("p -> q").unwrap();
        let pnf = to_positive_normal_form(&f);
        assert_eq!(
            pnf,
            LtlFormula::Or(
                Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into())))),
                Box::new(LtlFormula::Atomic("q".into())),
            )
        );
        assert!(is_positive_normal_form(&pnf));
    }

    #[test]
    fn test_pnf_complex_nested() {
        // G (request -> F response) should produce a PNF result
        let f = parse_ltl("G (request -> F response)").unwrap();
        let pnf = to_positive_normal_form(&f);
        assert!(is_positive_normal_form(&pnf));
    }

    #[test]
    fn test_pnf_atom_unchanged() {
        let f = LtlFormula::Atomic("p".into());
        let pnf = to_positive_normal_form(&f);
        assert_eq!(pnf, f);
        assert!(is_positive_normal_form(&pnf));
    }

    #[test]
    fn test_display_formula() {
        let f = parse_ltl("G (p -> F q)").unwrap();
        let s = f.to_string();
        assert!(s.contains('G'));
        assert!(s.contains('F'));
    }
}
