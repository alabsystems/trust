// trust-types/spec_attrs.rs: High-level specification attribute AST and parser
//
// Represents specification expressions before lowering to SMT-level Formula,
// enabling spec-level transformations such as inlining and strengthening.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::spec::SpecParseError;
use crate::spec_parse::{Token, literal_index_spellings_are_canonical, tokenize};
use crate::{Formula, Sort};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SpecExpr {
    BoolLit(bool),
    IntLit(i128),
    /// An unsigned literal that cannot necessarily be represented by `i128`.
    UIntLit(u128),
    /// An IEEE-754 binary64 literal, stored as its raw bits so the AST keeps
    /// `Eq` (mirrors `Token::Float`); lowered to
    /// `Formula::FpConst { eb: 11, sb: 53 }`.
    FloatLit(u64),
    Var(String),
    BinOp {
        lhs: Box<SpecExpr>,
        op: SpecBinOp,
        rhs: Box<SpecExpr>,
    },
    UnaryOp {
        op: SpecUnaryOp,
        expr: Box<SpecExpr>,
    },
    FnCall {
        name: String,
        args: Vec<SpecExpr>,
    },
    Forall {
        var: String,
        ty: String,
        body: Box<SpecExpr>,
    },
    Exists {
        var: String,
        ty: String,
        body: Box<SpecExpr>,
    },
    Old(Box<SpecExpr>),
    Result,
    Field {
        base: Box<SpecExpr>,
        field: String,
    },
    /// A zero-argument method call such as `xs.len()`.
    ///
    /// Keep this distinct from [`SpecExpr::Field`]. Rust permits both a field
    /// `x.len` and a method `x.len()`, and the executable Formula parser gives
    /// them deliberately different meanings (`x.len` versus the modeled
    /// collection-length leaf `x_len`).
    MethodCall {
        base: Box<SpecExpr>,
        method: String,
    },
    Index {
        base: Box<SpecExpr>,
        index: Box<SpecExpr>,
    },
    Implies {
        lhs: Box<SpecExpr>,
        rhs: Box<SpecExpr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SpecBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SpecUnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HighLevelSpecAttr {
    Requires(SpecExpr),
    Ensures(SpecExpr),
    Invariant(SpecExpr),
    Decreases(SpecExpr),
    Pure,
    Trusted,
}

pub fn parse_spec_attr(
    attr_name: &str,
    content: &str,
) -> Result<HighLevelSpecAttr, SpecParseError> {
    match attr_name {
        "pure" => Ok(HighLevelSpecAttr::Pure),
        "trusted" => Ok(HighLevelSpecAttr::Trusted),
        "requires" => parse_spec_expr(content).map(HighLevelSpecAttr::Requires),
        "ensures" => parse_spec_expr(content).map(HighLevelSpecAttr::Ensures),
        "invariant" => parse_spec_expr(content).map(HighLevelSpecAttr::Invariant),
        "decreases" => parse_spec_expr(content).map(HighLevelSpecAttr::Decreases),
        _ => Err(SpecParseError::UnexpectedToken {
            position: 0,
            expected: "known spec attribute name".into(),
        }),
    }
}

/// Convert the public high-level specification AST to the executable Formula
/// vocabulary without erasing source distinctions.
///
/// Conversion is fallible because an unknown function/method call, an
/// unsupported typed quantifier domain, or a projection without a stable
/// Formula place name must not be replaced by a free leaf. Such replacement
/// is non-injective and can collapse a false source relation into reflexivity.
pub fn try_spec_expr_to_formula(expr: &SpecExpr) -> Result<Formula, SpecParseError> {
    spec_expr_to_formula_with_bound_sorts(expr, &mut Vec::new())
}

/// Legacy infallible compatibility entry point.
///
/// This wrapper deliberately fails stop if the high-level AST cannot be
/// represented exactly. It never restores the historical behavior that
/// erased call arguments or projections. New code should handle
/// [`try_spec_expr_to_formula`] explicitly.
#[deprecated(note = "use try_spec_expr_to_formula and handle unsupported source forms")]
pub fn spec_expr_to_formula(expr: &SpecExpr) -> Formula {
    try_spec_expr_to_formula(expr).expect(
        "spec_expr_to_formula cannot lower this source AST exactly; use \
         try_spec_expr_to_formula to handle the error",
    )
}

fn spec_expr_to_formula_with_bound_sorts(
    expr: &SpecExpr,
    bound_sorts: &mut Vec<(String, Sort)>,
) -> Result<Formula, SpecParseError> {
    match expr {
        SpecExpr::BoolLit(value) => Ok(Formula::Bool(*value)),
        SpecExpr::IntLit(value) => Ok(Formula::Int(*value)),
        SpecExpr::UIntLit(value) => Ok(Formula::UInt(*value)),
        // The bits round-trip exactly; `{ eb: 11, sb: 53 }` is the binary64
        // format, matching the executable formula parser's float-literal atom.
        SpecExpr::FloatLit(bits) => {
            Ok(Formula::FpConst { bits: u128::from(*bits), eb: 11, sb: 53 })
        }
        SpecExpr::Var(name) => {
            // Parsed dereferences retain their canonical Formula suffix in the
            // compact public AST (`*x` -> `Var("x*")`).  Validate the actual
            // source binding before admitting either parsed or
            // programmatically constructed nodes.
            let source_name = name.trim_end_matches('*');
            if !crate::spec_parse::is_plain_source_binding_name(source_name) {
                return Err(SpecParseError::UnexpectedToken {
                    position: 0,
                    expected: "a non-reserved plain source binding".into(),
                });
            }
            let sort = bound_sorts
                .iter()
                .rev()
                .find_map(|(bound, sort)| (bound == source_name).then(|| sort.clone()))
                .unwrap_or(Sort::Int);
            Ok(Formula::Var(name.clone(), sort))
        }
        SpecExpr::BinOp { lhs, op, rhs } => {
            let lhs = Box::new(spec_expr_to_formula_with_bound_sorts(lhs, bound_sorts)?);
            let rhs = Box::new(spec_expr_to_formula_with_bound_sorts(rhs, bound_sorts)?);

            Ok(match op {
                SpecBinOp::Add => Formula::Add(lhs, rhs),
                SpecBinOp::Sub => Formula::Sub(lhs, rhs),
                SpecBinOp::Mul => Formula::Mul(lhs, rhs),
                SpecBinOp::Div => Formula::Div(lhs, rhs),
                SpecBinOp::Mod => Formula::Rem(lhs, rhs),
                SpecBinOp::Eq => Formula::Eq(lhs, rhs),
                SpecBinOp::Ne => Formula::Not(Box::new(Formula::Eq(lhs, rhs))),
                SpecBinOp::Lt => Formula::Lt(lhs, rhs),
                SpecBinOp::Le => Formula::Le(lhs, rhs),
                SpecBinOp::Gt => Formula::Gt(lhs, rhs),
                SpecBinOp::Ge => Formula::Ge(lhs, rhs),
                SpecBinOp::And => crate::spec_parse::canonical_and(vec![*lhs, *rhs]),
                SpecBinOp::Or => crate::spec_parse::canonical_or(vec![*lhs, *rhs]),
            })
        }
        SpecExpr::UnaryOp { op, expr } => {
            match op {
                SpecUnaryOp::Not => Ok(Formula::Not(Box::new(
                    spec_expr_to_formula_with_bound_sorts(expr, bound_sorts)?,
                ))),
                SpecUnaryOp::Neg => Ok(Formula::Neg(Box::new(
                    spec_expr_to_formula_with_bound_sorts(expr, bound_sorts)?,
                ))),
            }
        }
        SpecExpr::FnCall { name, args } => {
            // Trust SAFE_API §3: a closed-vocabulary predicate call lowers to an
            // uninterpreted Pred, consistent with the string spec parser
            // (spec_parse.rs) — otherwise the same `dir_open(dir)` text would
            // lower to a free Var here and a Pred there. A non-vocabulary call
            // is rejected: dropping its arguments made `f(x) == f(y)` become
            // `f == f`, a false proof.
            match crate::pred_arg_sorts(name.as_str()) {
                Some(sorts) if crate::is_valid_pred(name.as_str(), args.len()) => {
                    let pred_args = args
                        .iter()
                        .zip(sorts.iter())
                        .map(|(arg, sort)| {
                            Ok(match spec_expr_to_formula_with_bound_sorts(arg, bound_sorts)? {
                                Formula::Var(n, _) => Formula::Var(n, sort.clone()),
                                other => other,
                            })
                        })
                        .collect::<Result<Vec<_>, SpecParseError>>()?;
                    Ok(Formula::Pred(crate::Symbol::intern(name.as_str()), pred_args))
                }
                _ => Err(SpecParseError::UnsupportedMethod { method: name.clone() }),
            }
        }
        SpecExpr::Forall { var, ty, body } => {
            lower_spec_quantifier(true, var, ty, body, bound_sorts)
        }
        SpecExpr::Exists { var, ty, body } => {
            lower_spec_quantifier(false, var, ty, body, bound_sorts)
        }
        SpecExpr::Old(inner) => match inner.as_ref() {
            SpecExpr::Var(name) if crate::spec_parse::is_plain_source_binding_name(name) => {
                Ok(Formula::Var(format!("old_{name}"), Sort::Int))
            }
            _ => Err(SpecParseError::UnexpectedToken {
                position: 0,
                expected: "a plain variable inside old()".into(),
            }),
        },
        SpecExpr::Result => Ok(Formula::Var("_0".to_string(), Sort::Int)),
        SpecExpr::Field { base, field } => crate::spec_parse::field_projection(
            spec_expr_to_formula_with_bound_sorts(base, bound_sorts)?,
            field,
            0,
        ),
        SpecExpr::MethodCall { base, method } => crate::spec_parse::map_method_call(
            spec_expr_to_formula_with_bound_sorts(base, bound_sorts)?,
            method,
        ),
        SpecExpr::Index { base, index } => {
            let base = spec_expr_to_formula_with_bound_sorts(base, bound_sorts)?;
            let index = spec_expr_to_formula_with_bound_sorts(index, bound_sorts)?;
            Ok(match (base, index) {
                // Keep literal stable-place projections byte-identical to the
                // executable parser and MIR place naming. Computed indexing
                // retains its structural Select and is never collapsed into a
                // synthetic free variable.
                (Formula::Var(name, sort), Formula::Int(index)) if index >= 0 => {
                    Formula::Var(format!("{name}[{index}]"), sort)
                }
                (base, index) => Formula::Select(Box::new(base), Box::new(index)),
            })
        }
        SpecExpr::Implies { lhs, rhs } => Ok(Formula::Implies(
            Box::new(spec_expr_to_formula_with_bound_sorts(lhs, bound_sorts)?),
            Box::new(spec_expr_to_formula_with_bound_sorts(rhs, bound_sorts)?),
        )),
    }
}

fn lower_spec_quantifier(
    is_forall: bool,
    var: &str,
    ty: &str,
    body: &SpecExpr,
    bound_sorts: &mut Vec<(String, Sort)>,
) -> Result<Formula, SpecParseError> {
    let label = if is_forall { "forall" } else { "exists" };
    if !crate::spec_parse::is_plain_source_binding_name(var) {
        return Err(SpecParseError::InvalidQuantifier {
            detail: format!("{label}: invalid or reserved binder `{var}`"),
        });
    }
    let (sort, domain) =
        crate::spec_parse::typed_quantifier_domain(ty, is_forall).ok_or_else(|| {
            SpecParseError::InvalidQuantifier {
                detail: format!("{label}: unsupported binder type `{ty}`"),
            }
        })?;
    bound_sorts.push((var.to_string(), sort.clone()));
    let lowered_body = spec_expr_to_formula_with_bound_sorts(body, bound_sorts);
    bound_sorts.pop();
    let mut lowered_body = lowered_body?;
    if let Some(domain) = domain {
        let guard = domain.guard(Formula::Var(var.to_string(), sort.clone()));
        lowered_body = if is_forall {
            Formula::Implies(Box::new(guard), Box::new(lowered_body))
        } else {
            crate::spec_parse::canonical_and(vec![guard, lowered_body])
        };
    }
    let bindings = vec![(crate::Symbol::intern(var), sort)];
    Ok(if is_forall {
        Formula::Forall(bindings, Box::new(lowered_body))
    } else {
        Formula::Exists(bindings, Box::new(lowered_body))
    })
}

fn parse_spec_expr(input: &str) -> Result<SpecExpr, SpecParseError> {
    if input.trim().is_empty() {
        return Err(SpecParseError::Empty);
    }
    if !literal_index_spellings_are_canonical(input) {
        return Err(SpecParseError::UnexpectedToken {
            position: 0,
            expected: "canonical nonnegative literal index spelling".into(),
        });
    }

    let tokens = tokenize(input)?;
    let mut parser = SpecExprParser::new(tokens);
    let expr = parser.parse_implies()?;

    if parser.is_eof() { Ok(expr) } else { Err(SpecParseError::TrailingTokens) }
}

struct SpecExprParser {
    tokens: Vec<Token>,
    index: usize,
}

impl SpecExprParser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, index: 0 }
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
            .inspect(|_| {
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

    fn parse_implies(&mut self) -> Result<SpecExpr, SpecParseError> {
        let lhs = self.parse_or()?;

        if self.eat(&Token::Implies) {
            let rhs = self.parse_implies()?;
            Ok(SpecExpr::Implies { lhs: Box::new(lhs), rhs: Box::new(rhs) })
        } else {
            Ok(lhs)
        }
    }

    fn parse_or(&mut self) -> Result<SpecExpr, SpecParseError> {
        self.parse_left_assoc(Self::parse_and, &[(Token::OrOr, SpecBinOp::Or)])
    }

    fn parse_and(&mut self) -> Result<SpecExpr, SpecParseError> {
        self.parse_left_assoc(Self::parse_comparison, &[(Token::AndAnd, SpecBinOp::And)])
    }

    fn parse_comparison(&mut self) -> Result<SpecExpr, SpecParseError> {
        let lhs = self.parse_add_sub()?;

        let Some(op) = self.peek().and_then(token_to_comparison_op) else {
            return Ok(lhs);
        };

        self.bump()?;
        let rhs = self.parse_add_sub()?;
        Ok(SpecExpr::BinOp { lhs: Box::new(lhs), op, rhs: Box::new(rhs) })
    }

    fn parse_add_sub(&mut self) -> Result<SpecExpr, SpecParseError> {
        self.parse_left_assoc(
            Self::parse_mul_div,
            &[(Token::Plus, SpecBinOp::Add), (Token::Minus, SpecBinOp::Sub)],
        )
    }

    fn parse_mul_div(&mut self) -> Result<SpecExpr, SpecParseError> {
        self.parse_left_assoc(
            Self::parse_unary,
            &[
                (Token::Star, SpecBinOp::Mul),
                (Token::Slash, SpecBinOp::Div),
                (Token::Percent, SpecBinOp::Mod),
            ],
        )
    }

    fn parse_unary(&mut self) -> Result<SpecExpr, SpecParseError> {
        if self.eat(&Token::Bang) {
            let expr = self.parse_unary()?;
            Ok(SpecExpr::UnaryOp { op: SpecUnaryOp::Not, expr: Box::new(expr) })
        } else if self.eat(&Token::Minus) {
            let expr = self.parse_unary()?;
            // `-<float literal>` folds into a sign-flipped f64 literal, exactly
            // like the executable formula parser's `FpConst` fold: a plain `Neg`
            // is Int-typed by the source sort checker, which would mis-type the
            // lower half of a two-sided float magnitude bound
            // (`(self.0) >= (-(1.0e30))`) and fail-closed every such contract.
            if let SpecExpr::FloatLit(bits) = expr {
                return Ok(SpecExpr::FloatLit((-f64::from_bits(bits)).to_bits()));
            }
            Ok(SpecExpr::UnaryOp { op: SpecUnaryOp::Neg, expr: Box::new(expr) })
        } else if self.eat(&Token::Star) {
            let expr = self.parse_unary()?;
            match expr {
                // Keep dereference provenance without expanding the public
                // verifier-API unary vocabulary: the canonical Formula layer
                // already spells a dereferenced source binding as `name*`.
                SpecExpr::Var(name) => Ok(SpecExpr::Var(format!("{name}*"))),
                _ => Err(SpecParseError::UnexpectedToken {
                    position: self.index.saturating_sub(1),
                    expected: "a named parameter after unary '*'".into(),
                }),
            }
        } else {
            self.parse_postfix()
        }
    }

    fn parse_postfix(&mut self) -> Result<SpecExpr, SpecParseError> {
        let mut expr = self.parse_atom()?;

        loop {
            if self.eat(&Token::Dot) {
                let field = match self.bump()? {
                    Token::Ident(name) => name,
                    // A numeric tuple-field projection `t.0`, mirroring the
                    // executable formula parser: the MIR names a `Field(i)`
                    // projection `<base>.i`, so `self.0` must survive this AST
                    // to validate the canonicalized float contracts. A numeric
                    // field is never a call (`t.0()` does not exist).
                    Token::Int(index) => index.to_string(),
                    _ => {
                        return Err(SpecParseError::UnexpectedToken {
                            position: self.index.saturating_sub(1),
                            expected: "field name or tuple index after '.'".into(),
                        });
                    }
                };

                if field.bytes().all(|byte| byte.is_ascii_digit()) {
                    // Numeric tuple fields cannot be invoked as methods.
                    expr = SpecExpr::Field { base: Box::new(expr), field };
                } else if self.eat(&Token::LParen) {
                    self.expect(&Token::RParen, "')' after field access")?;
                    expr = SpecExpr::MethodCall { base: Box::new(expr), method: field };
                } else {
                    expr = SpecExpr::Field { base: Box::new(expr), field };
                }
                continue;
            }

            if self.eat(&Token::LBracket) {
                let index = self.parse_implies()?;
                self.expect(&Token::RBracket, "closing ']'")?;
                expr = SpecExpr::Index { base: Box::new(expr), index: Box::new(index) };
                continue;
            }

            return Ok(expr);
        }
    }

    fn parse_atom(&mut self) -> Result<SpecExpr, SpecParseError> {
        match self.bump()? {
            Token::Ident(name) => self.parse_ident(name),
            Token::Int(value) => Ok(SpecExpr::IntLit(value)),
            // An f64 literal (`1.0e30`); the bits round-trip exactly through
            // the token, matching the executable formula parser's atom.
            Token::Float(bits) => Ok(SpecExpr::FloatLit(bits)),
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

    fn parse_ident(&mut self, name: String) -> Result<SpecExpr, SpecParseError> {
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
            return match crate::spec_parse::primitive_integer_constant(&name, &constant) {
                Some(Formula::Int(value)) => Ok(SpecExpr::IntLit(value)),
                Some(Formula::UInt(value)) => Ok(SpecExpr::UIntLit(value)),
                _ => Err(SpecParseError::UnexpectedToken {
                    position: self.index.saturating_sub(1),
                    expected: "fixed-width primitive integer MIN or MAX".into(),
                }),
            };
        }

        match name.as_str() {
            "true" => Ok(SpecExpr::BoolLit(true)),
            "false" => Ok(SpecExpr::BoolLit(false)),
            "result" => Ok(SpecExpr::Result),
            "old" if self.peek() == Some(&Token::LParen) => {
                self.expect(&Token::LParen, "'(' after old")?;
                let expr = self.parse_implies()?;
                self.expect(&Token::RParen, "closing ')' for old()")?;
                Ok(SpecExpr::Old(Box::new(expr)))
            }
            // Compiler-native clauses use the Lean-shaped binder spelling
            // `forall i: T, P` / `exists i: T, P` without parentheses. Keep it
            // in the high-level source AST too so the always-on source
            // scope/sort validator and the executable formula parser accept
            // the same first-class syntax.
            "forall" if matches!(self.peek(), Some(Token::Ident(_))) => {
                self.parse_native_typed_quantifier(true)
            }
            "exists" if matches!(self.peek(), Some(Token::Ident(_))) => {
                self.parse_native_typed_quantifier(false)
            }
            "forall" if self.peek() == Some(&Token::LParen) => self.parse_quantifier(true),
            "exists" if self.peek() == Some(&Token::LParen) => self.parse_quantifier(false),
            _ if self.peek() == Some(&Token::LParen) => self.parse_fn_call(name),
            _ => Ok(SpecExpr::Var(name)),
        }
    }

    fn parse_fn_call(&mut self, name: String) -> Result<SpecExpr, SpecParseError> {
        self.expect(&Token::LParen, &format!("'(' after function name '{name}'"))?;
        let mut args = Vec::new();

        if !self.eat(&Token::RParen) {
            loop {
                args.push(self.parse_implies()?);
                if self.eat(&Token::Comma) {
                    continue;
                }

                self.expect(&Token::RParen, "closing ')' after function call")?;
                break;
            }
        }

        Ok(SpecExpr::FnCall { name, args })
    }

    fn parse_native_typed_quantifier(
        &mut self,
        is_forall: bool,
    ) -> Result<SpecExpr, SpecParseError> {
        let label = if is_forall { "forall" } else { "exists" };
        let mut vars = Vec::new();
        while let Some(Token::Ident(_)) = self.peek() {
            let Token::Ident(var) = self.bump()? else { unreachable!() };
            if !crate::spec_parse::is_plain_source_binding_name(&var) || vars.contains(&var) {
                return Err(SpecParseError::InvalidQuantifier {
                    detail: format!("{label}: invalid or duplicate binder `{var}`"),
                });
            }
            vars.push(var);
            if self.peek() == Some(&Token::Colon) {
                break;
            }
        }
        if vars.is_empty() {
            return Err(SpecParseError::InvalidQuantifier {
                detail: format!("{label}: expected a binder name"),
            });
        }
        self.expect(&Token::Colon, &format!("':' after binders in {label}"))?;
        let ty = match self.bump()? {
            Token::Ident(name) => name,
            _ => {
                return Err(SpecParseError::InvalidQuantifier {
                    detail: format!("{label}: expected type name"),
                });
            }
        };
        self.expect(&Token::Comma, &format!("',' after type in {label}"))?;
        let mut body = self.parse_implies()?;
        // `SpecExpr` stores one binder per node. Desugar the ratified grouped
        // spelling to nested binders in source order; this is logically exact
        // and lets the source sort checker restore each lexical scope.
        for var in vars.into_iter().rev() {
            body = if is_forall {
                SpecExpr::Forall { var, ty: ty.clone(), body: Box::new(body) }
            } else {
                SpecExpr::Exists { var, ty: ty.clone(), body: Box::new(body) }
            };
        }
        Ok(body)
    }

    fn parse_quantifier(&mut self, is_forall: bool) -> Result<SpecExpr, SpecParseError> {
        let label = if is_forall { "forall" } else { "exists" };
        self.expect(&Token::LParen, &format!("'(' after {label}"))?;

        let var = match self.bump()? {
            Token::Ident(name) => name,
            _ => {
                return Err(SpecParseError::InvalidQuantifier {
                    detail: format!("{label}: expected variable name"),
                });
            }
        };
        if !crate::spec_parse::is_plain_source_binding_name(&var) {
            return Err(SpecParseError::InvalidQuantifier {
                detail: format!("{label}: invalid or reserved binder `{var}`"),
            });
        }

        if self.eat(&Token::Colon) {
            let ty = match self.bump()? {
                Token::Ident(name) => name,
                _ => {
                    return Err(SpecParseError::InvalidQuantifier {
                        detail: format!("{label}: expected type name"),
                    });
                }
            };

            self.expect(&Token::Comma, &format!("',' after type in {label}"))?;
            let body = self.parse_implies()?;
            self.expect(&Token::RParen, &format!("closing ')' for {label}"))?;
            return Ok(if is_forall {
                SpecExpr::Forall { var, ty, body: Box::new(body) }
            } else {
                SpecExpr::Exists { var, ty, body: Box::new(body) }
            });
        }

        // Attribute-compatibility parser only. First-class compiler-native
        // clauses use Lean-shaped `forall i: T, P` / `exists i: T, P` and are
        // lowered by the compiler snippet parser. Legacy attributes may still
        // carry bounded `forall(i, lo..hi, P)` / `exists(i, lo..hi, P)`; retain
        // that migration spelling here and desugar exactly as the executable
        // formula parser does so both compatibility consumers see one meaning:
        //
        //   forall i in [lo, hi): range(i) => P
        //   exists i in [lo, hi): range(i) && P
        if !self.eat(&Token::Comma) {
            return Err(SpecParseError::InvalidQuantifier {
                detail: format!("{label}: expected ':' or ',' after variable"),
            });
        }
        let lo = self.parse_add_sub()?;
        if !self.eat(&Token::DotDot) {
            return Err(SpecParseError::InvalidQuantifier {
                detail: format!("{label}: expected '..' in range"),
            });
        }
        let hi = self.parse_add_sub()?;
        self.expect(&Token::Comma, &format!("',' after range in {label}"))?;
        let body = self.parse_implies()?;
        self.expect(&Token::RParen, &format!("closing ')' for {label}"))?;

        let bound = SpecExpr::Var(var.clone());
        let range = SpecExpr::BinOp {
            lhs: Box::new(SpecExpr::BinOp {
                lhs: Box::new(lo),
                op: SpecBinOp::Le,
                rhs: Box::new(bound.clone()),
            }),
            op: SpecBinOp::And,
            rhs: Box::new(SpecExpr::BinOp {
                lhs: Box::new(bound),
                op: SpecBinOp::Lt,
                rhs: Box::new(hi),
            }),
        };
        let body = if is_forall {
            SpecExpr::Implies { lhs: Box::new(range), rhs: Box::new(body) }
        } else {
            SpecExpr::BinOp { lhs: Box::new(range), op: SpecBinOp::And, rhs: Box::new(body) }
        };
        Ok(if is_forall {
            SpecExpr::Forall { var, ty: "int".to_string(), body: Box::new(body) }
        } else {
            SpecExpr::Exists { var, ty: "int".to_string(), body: Box::new(body) }
        })
    }

    fn parse_left_assoc(
        &mut self,
        parser: fn(&mut Self) -> Result<SpecExpr, SpecParseError>,
        ops: &[(Token, SpecBinOp)],
    ) -> Result<SpecExpr, SpecParseError> {
        let mut expr = parser(self)?;

        loop {
            let Some(op) =
                ops.iter().find_map(|(token, op)| (self.peek() == Some(token)).then_some(*op))
            else {
                return Ok(expr);
            };

            self.bump()?;
            let rhs = parser(self)?;
            expr = SpecExpr::BinOp { lhs: Box::new(expr), op, rhs: Box::new(rhs) };
        }
    }
}

fn token_to_comparison_op(token: &Token) -> Option<SpecBinOp> {
    match token {
        Token::EqEq => Some(SpecBinOp::Eq),
        Token::Ne => Some(SpecBinOp::Ne),
        Token::Lt => Some(SpecBinOp::Lt),
        Token::Le => Some(SpecBinOp::Le),
        Token::Gt => Some(SpecBinOp::Gt),
        Token::Ge => Some(SpecBinOp::Ge),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> SpecExpr {
        SpecExpr::Var(name.to_string())
    }

    fn int(value: i128) -> SpecExpr {
        SpecExpr::IntLit(value)
    }

    fn require_formula(source: &str) -> Result<Formula, SpecParseError> {
        let HighLevelSpecAttr::Requires(expr) = parse_spec_attr("requires", source)? else {
            unreachable!("requires parser always returns Requires")
        };
        try_spec_expr_to_formula(&expr)
    }

    fn assert_executable_formula_parity(source: &str) {
        assert_eq!(
            require_formula(source).unwrap(),
            crate::parse_spec_expr_result(source).unwrap(),
            "high-level and executable Formula lowering drifted for `{source}`",
        );
    }

    #[test]
    fn spec_attrs_parses_simple_requires() {
        let attr = parse_spec_attr("requires", "x > 0").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::BinOp {
                lhs: Box::new(var("x")),
                op: SpecBinOp::Gt,
                rhs: Box::new(int(0)),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_ensures_with_result() {
        let attr = parse_spec_attr("ensures", "result >= x").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Ensures(SpecExpr::BinOp {
                lhs: Box::new(SpecExpr::Result),
                op: SpecBinOp::Ge,
                rhs: Box::new(var("x")),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_compound_and() {
        let attr = parse_spec_attr("requires", "x > 0 && y > 0").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::BinOp {
                lhs: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("x")),
                    op: SpecBinOp::Gt,
                    rhs: Box::new(int(0)),
                }),
                op: SpecBinOp::And,
                rhs: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("y")),
                    op: SpecBinOp::Gt,
                    rhs: Box::new(int(0)),
                }),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_forall() {
        let attr = parse_spec_attr("requires", "forall(i: int, i >= 0)").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::Forall {
                var: "i".to_string(),
                ty: "int".to_string(),
                body: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("i")),
                    op: SpecBinOp::Ge,
                    rhs: Box::new(int(0)),
                }),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_native_typed_quantifier_with_indexing() {
        let attr =
            parse_spec_attr("invariant", "forall i j: usize, i < j && j < lo ==> xs[i] <= xs[j]")
                .expect("native typed quantifier should parse");
        let HighLevelSpecAttr::Invariant(SpecExpr::Forall { var, ty, body }) = attr else {
            panic!("expected outer native forall binder");
        };
        assert_eq!(var, "i");
        assert_eq!(ty, "usize");
        assert!(matches!(
            body.as_ref(),
            SpecExpr::Forall { var, ty, .. } if var == "j" && ty == "usize"
        ));
    }

    #[test]
    fn spec_attrs_grouped_and_parenthesized_typed_quantifiers_have_exact_formula_parity() {
        for source in [
            "forall(i: int, i == i)",
            "forall(b: bool, b || !b)",
            "exists(i: u8, i == 255)",
            "forall i j: u8, i <= j",
            "exists x y: bool, x || y",
        ] {
            assert_executable_formula_parity(source);
        }

        let formula = crate::parse_spec_expr_result("forall i j: bool, i || !i").unwrap();
        let Formula::Forall(outer, body) = formula else { panic!("expected outer forall") };
        assert_eq!(outer.len(), 1, "grouped syntax canonicalizes to one binder per node");
        assert!(matches!(*body, Formula::Forall(ref inner, _) if inner.len() == 1));
    }

    #[test]
    fn spec_attrs_parses_bounded_quantifiers_with_formula_parser_parity() {
        for (kind, source) in [
            ("ensures", "forall(i, 0..n, i < n => result >= old(x))"),
            ("requires", "exists(j, lo..hi, j == x)"),
        ] {
            let attr = parse_spec_attr(kind, source).expect("bounded quantifier should parse");
            let expr = match attr {
                HighLevelSpecAttr::Requires(expr) | HighLevelSpecAttr::Ensures(expr) => expr,
                other => panic!("unexpected attribute: {other:?}"),
            };
            assert_eq!(
                try_spec_expr_to_formula(&expr).expect("high-level AST should lower exactly"),
                crate::parse_spec_expr(source).expect("formula parser should accept same source"),
                "the public verifier AST and executable formula parser must agree for {source}",
            );
        }
    }

    #[test]
    fn spec_attrs_rejects_malformed_bounded_quantifiers() {
        for source in [
            "forall(i, 0, i == i)",
            "forall(i, 0..n i == i)",
            "exists(i, 0..n, i == i",
            "exists(0, 0..n, true)",
        ] {
            assert!(
                parse_spec_attr("ensures", source).is_err(),
                "malformed bounded quantifier must be rejected: {source}",
            );
        }
    }

    #[test]
    fn spec_attrs_rejects_synthetic_contract_binders() {
        for name in [
            "_0",
            "_2",
            "old_x",
            "xs_len",
            "x_discr",
            "x_value",
            "x_sign",
            "priv_dropped",
            "s__slice_len",
            "__trust_constparam_0_N",
        ] {
            for source in
                [format!("forall {name}: u64, true"), format!("forall({name}, 0..1, true)")]
            {
                assert!(
                    matches!(
                        parse_spec_attr("invariant", &source),
                        Err(SpecParseError::InvalidQuantifier { .. })
                    ),
                    "synthetic binder must be rejected: {source}",
                );
            }
        }
    }

    #[test]
    fn spec_attrs_parses_old() {
        let attr = parse_spec_attr("ensures", "old(x) <= result").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Ensures(SpecExpr::BinOp {
                lhs: Box::new(SpecExpr::Old(Box::new(var("x")))),
                op: SpecBinOp::Le,
                rhs: Box::new(SpecExpr::Result),
            })
        );
    }

    #[test]
    fn spec_attrs_old_rejects_every_reserved_or_synthetic_operand() {
        for name in [
            "true",
            "false",
            "result",
            "forall",
            "exists",
            "priv_dropped",
            "old_x",
            "xs_len",
            "_0",
            "_2",
            "s__slice_len",
        ] {
            let source = format!("old({name}) == 0");
            assert!(require_formula(&source).is_err(), "high-level old operand admitted: {name}");
            assert!(
                crate::parse_spec_expr_result(&source).is_err(),
                "executable old operand admitted: {name}"
            );
        }
        assert_executable_formula_parity("old(x) == 0");
    }

    #[test]
    fn spec_attrs_programmatic_vars_and_binders_reject_reserved_namespace() {
        for name in [
            "true",
            "false",
            "result",
            "forall",
            "exists",
            "priv_dropped",
            "old_x",
            "xs_len",
            "_0",
            "_2",
            "s__slice_len",
        ] {
            assert!(
                try_spec_expr_to_formula(&SpecExpr::Var(name.to_string())).is_err(),
                "programmatic Var admitted reserved name `{name}`"
            );
            assert!(
                try_spec_expr_to_formula(&SpecExpr::Forall {
                    var: name.to_string(),
                    ty: "int".to_string(),
                    body: Box::new(SpecExpr::BoolLit(true)),
                })
                .is_err(),
                "programmatic binder admitted reserved name `{name}`"
            );
        }

        for source in [
            "priv_dropped == priv_dropped",
            "old_x == old_x",
            "xs_len == xs_len",
            "_2 == _2",
            "forall + 1 == 2",
            "exists + 1 == 2",
        ] {
            assert!(require_formula(source).is_err());
            assert!(crate::parse_spec_expr_result(source).is_err());
        }
    }

    #[test]
    #[allow(deprecated)]
    fn spec_attrs_legacy_converter_is_compatible_but_fails_stop() {
        let valid = SpecExpr::BoolLit(true);
        assert_eq!(spec_expr_to_formula(&valid), try_spec_expr_to_formula(&valid).unwrap());

        let unsupported =
            SpecExpr::FnCall { name: "attacker_defined".to_string(), args: vec![var("x")] };
        assert!(std::panic::catch_unwind(|| spec_expr_to_formula(&unsupported)).is_err());
    }

    #[test]
    fn spec_attrs_boolean_chains_are_canonical_nary_in_both_parsers() {
        for source in [
            "a && b && c",
            "(a && b) && c",
            "a && (b && c)",
            "a || b || c",
            "(a || b) || c",
            "a || (b || c)",
        ] {
            assert_executable_formula_parity(source);
            let formula = require_formula(source).unwrap();
            assert!(
                matches!(formula, Formula::And(ref terms) | Formula::Or(ref terms) if terms.len() == 3),
                "Boolean chain was not canonicalized for `{source}`: {formula:?}"
            );
        }
    }

    #[test]
    fn spec_attrs_tuple_index_and_postfix_chains_have_exact_formula_parity() {
        for source in [
            "result.0 == result.1",
            "arr[i] == arr[j]",
            "matrix[i][j] == matrix[k][l]",
            "point.values[i] == point.values[j]",
            "result.0.items[2] == result.0.items[3]",
        ] {
            assert_executable_formula_parity(source);
        }

        // A Select has no stable MIR place name from which to mint a dotted
        // field/accessor leaf. Both lowering paths therefore fail closed.
        for source in ["arr[i].field == 0", "arr[i].len() == 0", "t.0() == 0"] {
            assert!(require_formula(source).is_err());
            assert!(crate::parse_spec_expr_result(source).is_err());
        }
    }

    #[test]
    fn spec_attrs_dereferenced_result_fails_closed_in_both_parsers() {
        for source in ["*result == result", "*_0 == result", "*x.field == 0"] {
            assert!(require_formula(source).is_err());
            assert!(crate::parse_spec_expr_result(source).is_err());
        }
        assert_executable_formula_parity("*x == *x");
        assert_executable_formula_parity("(*x).field == (*x).field");
    }

    #[test]
    fn spec_attrs_parses_nested_arithmetic() {
        let attr = parse_spec_attr("requires", "a + b * c - d").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::BinOp {
                lhs: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("a")),
                    op: SpecBinOp::Add,
                    rhs: Box::new(SpecExpr::BinOp {
                        lhs: Box::new(var("b")),
                        op: SpecBinOp::Mul,
                        rhs: Box::new(var("c")),
                    }),
                }),
                op: SpecBinOp::Sub,
                rhs: Box::new(var("d")),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_implies() {
        let attr = parse_spec_attr("ensures", "x > 0 => result > x").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Ensures(SpecExpr::Implies {
                lhs: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("x")),
                    op: SpecBinOp::Gt,
                    rhs: Box::new(int(0)),
                }),
                rhs: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(SpecExpr::Result),
                    op: SpecBinOp::Gt,
                    rhs: Box::new(var("x")),
                }),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_not() {
        let attr = parse_spec_attr("requires", "!(x == 0)").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::UnaryOp {
                op: SpecUnaryOp::Not,
                expr: Box::new(SpecExpr::BinOp {
                    lhs: Box::new(var("x")),
                    op: SpecBinOp::Eq,
                    rhs: Box::new(int(0)),
                }),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_pure() {
        let attr = parse_spec_attr("pure", "").expect("should parse");
        assert_eq!(attr, HighLevelSpecAttr::Pure);
    }

    #[test]
    fn spec_attrs_parses_trusted() {
        let attr = parse_spec_attr("trusted", "ignored").expect("should parse");
        assert_eq!(attr, HighLevelSpecAttr::Trusted);
    }

    #[test]
    fn spec_attrs_rejects_unknown_attr() {
        let err = parse_spec_attr("unknown", "x > 0").unwrap_err();
        assert_eq!(
            err,
            SpecParseError::UnexpectedToken {
                position: 0,
                expected: "known spec attribute name".into(),
            }
        );
    }

    #[test]
    fn spec_attrs_rejects_empty_content() {
        let err = parse_spec_attr("requires", "").unwrap_err();
        assert_eq!(err, SpecParseError::Empty);
    }

    #[test]
    fn spec_attrs_rejects_invalid_syntax() {
        let err = parse_spec_attr("requires", "x &&").unwrap_err();
        assert!(matches!(err, SpecParseError::UnexpectedEof { .. }));
    }

    #[test]
    fn spec_attrs_to_formula_basic() {
        let formula = try_spec_expr_to_formula(&SpecExpr::BoolLit(true)).unwrap();
        assert_eq!(formula, Formula::Bool(true));
    }

    #[test]
    fn spec_attrs_to_formula_comparison() {
        let expr =
            SpecExpr::BinOp { lhs: Box::new(var("x")), op: SpecBinOp::Lt, rhs: Box::new(int(1)) };
        let formula = try_spec_expr_to_formula(&expr).unwrap();
        assert_eq!(
            formula,
            Formula::Lt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )
        );
    }

    #[test]
    fn spec_attrs_to_formula_result() {
        let formula = try_spec_expr_to_formula(&SpecExpr::Result).unwrap();
        assert_eq!(formula, Formula::Var("_0".to_string(), Sort::Int));
    }

    #[test]
    fn spec_attrs_to_formula_old() {
        let formula = try_spec_expr_to_formula(&SpecExpr::Old(Box::new(var("x")))).unwrap();
        assert_eq!(formula, Formula::Var("old_x".to_string(), Sort::Int));
    }

    #[test]
    fn spec_attrs_to_formula_index() {
        let expr = SpecExpr::Index { base: Box::new(var("arr")), index: Box::new(var("i")) };
        let formula = try_spec_expr_to_formula(&expr).unwrap();
        assert_eq!(
            formula,
            Formula::Select(
                Box::new(Formula::Var("arr".to_string(), Sort::Int)),
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
            )
        );
    }

    #[test]
    fn spec_attrs_to_formula_field() {
        let expr = SpecExpr::Field { base: Box::new(var("point")), field: "x".to_string() };
        let formula = try_spec_expr_to_formula(&expr).unwrap();
        assert_eq!(formula, Formula::Var("point.x".to_string(), Sort::Int));
    }

    #[test]
    fn spec_attrs_field_lowering_is_injective_and_nested() {
        let attr = parse_spec_attr("requires", "p.x.y == p_x_y").unwrap();
        let HighLevelSpecAttr::Requires(expr) = attr else {
            panic!("expected requires expression");
        };
        let formula = try_spec_expr_to_formula(&expr).unwrap();
        let Formula::Eq(lhs, rhs) = formula else {
            panic!("expected equality");
        };
        assert_eq!(*lhs, Formula::Var("p.x.y".into(), Sort::Int));
        assert_eq!(*rhs, Formula::Var("p_x_y".into(), Sort::Int));
        assert_ne!(lhs, rhs, "an ordinary field must not alias an underscore-named source leaf");
    }

    #[test]
    fn spec_attrs_field_and_method_call_remain_distinct() {
        let attr = parse_spec_attr("requires", "x.len == x.len()").unwrap();
        let HighLevelSpecAttr::Requires(expr) = attr else {
            panic!("expected requires expression");
        };
        let SpecExpr::BinOp { lhs, rhs, .. } = &expr else {
            panic!("expected equality AST");
        };
        assert!(matches!(lhs.as_ref(), SpecExpr::Field { field, .. } if field == "len"));
        assert!(matches!(rhs.as_ref(), SpecExpr::MethodCall { method, .. } if method == "len"));

        let Formula::Eq(lhs, rhs) = try_spec_expr_to_formula(&expr).unwrap() else {
            panic!("expected equality Formula");
        };
        assert_eq!(*lhs, Formula::Var("x.len".into(), Sort::Int));
        assert_eq!(*rhs, Formula::Var("x_len".into(), Sort::Int));
        assert_ne!(lhs, rhs, "field syntax and method syntax must not collapse");
    }

    #[test]
    fn spec_attrs_unknown_calls_and_non_identifier_old_fail_closed() {
        for source in ["unknown(x)", "unknown(y)", "old(x + 1)", "old(*x)"] {
            let attr = parse_spec_attr("requires", source).unwrap();
            let HighLevelSpecAttr::Requires(expr) = attr else {
                panic!("expected requires expression");
            };
            assert!(
                try_spec_expr_to_formula(&expr).is_err(),
                "unsupported source form must not be erased: {source}"
            );
            assert!(
                crate::parse_spec_expr_result(source).is_err(),
                "the executable parser must reject the same source form: {source}"
            );
        }
    }

    #[test]
    fn spec_attrs_known_predicate_and_method_calls_match_executable_parser() {
        for source in ["dir_open(dir)", "xs.len() == 3", "result.is_none()"] {
            let attr = parse_spec_attr("requires", source).unwrap();
            let HighLevelSpecAttr::Requires(expr) = attr else {
                panic!("expected requires expression");
            };
            assert_eq!(
                try_spec_expr_to_formula(&expr).unwrap(),
                crate::parse_spec_expr_result(source).unwrap(),
                "high-level and executable lowering drifted for {source}"
            );
        }
    }

    #[test]
    fn spec_attrs_to_formula_forall() {
        let expr = SpecExpr::Forall {
            var: "i".to_string(),
            ty: "int".to_string(),
            body: Box::new(SpecExpr::BinOp {
                lhs: Box::new(var("i")),
                op: SpecBinOp::Ge,
                rhs: Box::new(int(0)),
            }),
        };
        let formula = try_spec_expr_to_formula(&expr).unwrap();
        assert_eq!(
            formula,
            Formula::Forall(
                vec![("i".into(), Sort::Int)],
                Box::new(Formula::Ge(
                    Box::new(Formula::Var("i".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            )
        );
    }

    #[test]
    fn spec_attrs_typed_quantifiers_match_sorts_and_domain_guards() {
        for source in
            ["forall b: bool, b || !b", "forall i: u8, i <= 255", "exists i: u8, i == 255"]
        {
            let attr = parse_spec_attr("requires", source).unwrap();
            let HighLevelSpecAttr::Requires(expr) = attr else {
                panic!("expected requires expression");
            };
            assert_eq!(
                try_spec_expr_to_formula(&expr).unwrap(),
                crate::parse_spec_expr_result(source).unwrap(),
                "typed quantifier lowering drifted for {source}"
            );
        }
    }

    #[test]
    fn spec_attrs_target_dependent_existentials_fail_closed() {
        for source in ["exists i: usize, i == 0", "exists i: isize, i == 0"] {
            let attr = parse_spec_attr("requires", source).unwrap();
            let HighLevelSpecAttr::Requires(expr) = attr else {
                panic!("expected requires expression");
            };
            assert!(try_spec_expr_to_formula(&expr).is_err());
            assert!(crate::parse_spec_expr_result(source).is_err());
        }
    }

    #[test]
    fn spec_attrs_parses_field_and_index() {
        let attr = parse_spec_attr("requires", "arr[i].len").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::Field {
                base: Box::new(SpecExpr::Index {
                    base: Box::new(var("arr")),
                    index: Box::new(var("i")),
                }),
                field: "len".to_string(),
            })
        );
    }

    #[test]
    fn spec_attrs_parses_numeric_tuple_fields_and_bracketed_chains() {
        // `t.0` — the numeric `Field(i)` spelling every canonicalized float
        // contract carries. Previously this was a hard "field name after '.'"
        // error, which made validate_source_spec_expr reject EVERY such
        // contract (the callee's requires then failed closed at all callers).
        let attr = parse_spec_attr("requires", "(t.0) <= (1.0e30)").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::BinOp {
                lhs: Box::new(SpecExpr::Field { base: Box::new(var("t")), field: "0".to_string() }),
                op: SpecBinOp::Le,
                rhs: Box::new(SpecExpr::FloatLit(1.0e30_f64.to_bits())),
            })
        );
        // A bracketed chain nests Field/Index positionally: self.0[3].1.
        let attr = parse_spec_attr("requires", "self.0[3].1 > 0").expect("should parse");
        let HighLevelSpecAttr::Requires(SpecExpr::BinOp { lhs, .. }) = attr else {
            panic!("expected comparison");
        };
        assert_eq!(
            *lhs,
            SpecExpr::Field {
                base: Box::new(SpecExpr::Index {
                    base: Box::new(SpecExpr::Field {
                        base: Box::new(var("self")),
                        field: "0".to_string(),
                    }),
                    index: Box::new(int(3)),
                }),
                field: "1".to_string(),
            }
        );
        assert!(
            parse_spec_attr("requires", "self.0[03].1 > 0").is_err(),
            "the high-level parser must not erase an alternate literal-index spelling",
        );
        assert!(
            parse_spec_attr("requires", "self.0[(3)].1 > 0").is_err(),
            "the high-level parser must not erase literal-index parentheses",
        );
        assert!(
            parse_spec_attr("requires", "self.00[3].1 > 0").is_err(),
            "the high-level parser must not erase an alternate tuple-field spelling",
        );
    }

    #[test]
    fn spec_attrs_numeric_field_is_never_a_call() {
        // MUST-NOT-PARSE twin: a numeric field has no call form (`t.0()` does
        // not exist), so the stray parens are a hard error — never a silently
        // accepted Field.
        assert!(parse_spec_attr("requires", "t.0() > 1").is_err());
    }

    #[test]
    fn spec_attrs_parses_float_literals_with_negation_fold() {
        // A float literal atom; previously Token::Float hit the parse_atom
        // catch-all and every float-bounded contract failed validation.
        let attr = parse_spec_attr("requires", "x <= 1.0e30").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::BinOp {
                lhs: Box::new(var("x")),
                op: SpecBinOp::Le,
                rhs: Box::new(SpecExpr::FloatLit(1.0e30_f64.to_bits())),
            })
        );
        // `-(1.0e30)` folds into a sign-flipped literal (never an Int-typed
        // Neg), matching the executable formula parser's FpConst fold.
        let attr = parse_spec_attr("requires", "x >= (-(1.0e30))").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::BinOp {
                lhs: Box::new(var("x")),
                op: SpecBinOp::Ge,
                rhs: Box::new(SpecExpr::FloatLit((-1.0e30_f64).to_bits())),
            })
        );
        // Lowering: FloatLit -> the binary64 FpConst, bits preserved exactly.
        assert_eq!(
            spec_expr_to_formula(&SpecExpr::FloatLit(2.5e-3_f64.to_bits())),
            Formula::FpConst { bits: u128::from(2.5e-3_f64.to_bits()), eb: 11, sb: 53 },
        );
    }

    #[test]
    fn spec_attrs_parses_function_call() {
        let attr = parse_spec_attr("requires", "pred(x, y + 1)").expect("should parse");
        assert_eq!(
            attr,
            HighLevelSpecAttr::Requires(SpecExpr::FnCall {
                name: "pred".to_string(),
                args: vec![
                    var("x"),
                    SpecExpr::BinOp {
                        lhs: Box::new(var("y")),
                        op: SpecBinOp::Add,
                        rhs: Box::new(int(1)),
                    },
                ],
            })
        );
    }

    #[test]
    fn spec_attrs_resolves_fixed_width_integer_constants_exactly() {
        let attr = parse_spec_attr("requires", "a <= u32::MAX - b").unwrap();
        let HighLevelSpecAttr::Requires(SpecExpr::BinOp { rhs, .. }) = attr else {
            panic!("expected comparison");
        };
        assert!(matches!(
            *rhs,
            SpecExpr::BinOp {
                lhs,
                op: SpecBinOp::Sub,
                ..
            } if *lhs == SpecExpr::IntLit(u32::MAX as i128)
        ));
        assert_eq!(
            try_spec_expr_to_formula(&SpecExpr::UIntLit(u128::MAX)).unwrap(),
            Formula::UInt(u128::MAX)
        );
    }

    #[test]
    fn spec_attrs_rejects_target_dependent_or_unknown_constants() {
        assert!(parse_spec_attr("requires", "a < usize::MAX").is_err());
        assert!(parse_spec_attr("requires", "a < u32::BOGUS").is_err());
    }
}
