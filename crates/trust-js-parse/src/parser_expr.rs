// trust-js-parse: expression grammar — assignment/conditional/binary/unary
// chains, LeftHandSide + optional chains, primaries, template literals,
// object/array literals, the two cover grammars with true reparse
// (CoverParenthesizedExpressionAndArrowParameterList,
// CoverCallExpressionAndAsyncArrowHead), formal parameters, binding
// patterns, and assignment-target conversion.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::ast::*;
use crate::lexer::{Fail, P, TokenKind, TplKind};
use crate::parser::{cook_string, BindTarget, Parser, ParamInfo, PResult, Pending, ScopeKind};
use crate::regex_validate::validate_regex;

impl Parser {
    // ---- expression entry points ---------------------------------------

    pub fn parse_expression(&mut self) -> PResult<Expr> {
        let first = self.parse_assignment(false)?;
        if !self.tok.is_punct(P::Comma) {
            return Ok(first);
        }
        let mut items = vec![first];
        while self.eat_punct(P::Comma)? {
            items.push(self.parse_assignment(false)?);
        }
        Ok(Expr::Seq(items))
    }

    pub fn parse_expression_statement_expr(&mut self) -> PResult<Expr> {
        self.parse_expression()
    }

    /// For-statement head expression: the first item may carry cover-only
    /// forms (they are resolved by for-in/of pattern conversion or raised by
    /// the caller for classic for).
    pub fn parse_for_head_expression(&mut self) -> PResult<Expr> {
        let first = self.parse_assignment(true)?;
        if !self.tok.is_punct(P::Comma) {
            return Ok(first);
        }
        if self.pending.any() {
            return Err(Fail::early("invalid shorthand property initializer"));
        }
        let mut items = vec![first];
        while self.eat_punct(P::Comma)? {
            items.push(self.parse_assignment(false)?);
        }
        Ok(Expr::Seq(items))
    }

    pub fn parse_assignment(&mut self, allow_cover: bool) -> PResult<Expr> {
        let g = self.enter()?;
        let saved = std::mem::take(&mut self.pending);
        let r = self.parse_assignment_inner();
        let r = match r {
            Ok(e) => {
                if !allow_cover && self.pending.any() {
                    Err(self.pending_error())
                } else {
                    Ok(e)
                }
            }
            e => e,
        };
        self.pending = Pending::merge_keep_earlier(saved, self.pending);
        self.leave(g);
        r
    }

    pub fn pending_error(&self) -> Fail {
        if self.pending.cover_init.is_some() {
            Fail::early("invalid shorthand property initializer")
        } else {
            Fail::early("duplicate __proto__ property in object literal")
        }
    }

    fn parse_assignment_inner(&mut self) -> PResult<Expr> {
        // YieldExpression.
        if self.ctx.yield_expr && self.tok.is_kw("yield") {
            return self.parse_yield();
        }
        // Arrow forms.
        if let TokenKind::Ident(name) = &self.tok.kind {
            let name = name.clone();
            if name == "async" && !self.tok.had_escape {
                let p = self.peek()?;
                if !p.newline_before {
                    if matches!(p.kind, TokenKind::Ident(_)) && !p.is_kw("function") {
                        let p2 = self.peek2()?;
                        if p2.is_punct(P::Arrow) && !p2.newline_before {
                            // async Ident => …
                            self.next()?; // async
                            return self.parse_arrow_single_ident(true);
                        }
                    }
                    if p.is_punct(P::LParen) {
                        return self.parse_async_paren();
                    }
                }
            }
            let p = self.peek()?;
            if p.is_punct(P::Arrow) && !p.newline_before {
                let _ = name;
                return self.parse_arrow_single_ident(false);
            }
        }
        if self.tok.is_punct(P::LParen) {
            return self.parse_paren_or_arrow();
        }
        // Ordinary path.
        let operand = if matches!(self.tok.kind, TokenKind::PrivateIdent(_)) {
            self.parse_private_ref_operand()?
        } else {
            self.parse_unary()?
        };
        let e = self.parse_binary_from(operand, 0)?;
        if matches!(e, Expr::PrivateRef(_)) {
            return Err(Fail::early("private name must be the left operand of 'in'"));
        }
        let e = self.parse_cond_from(e)?;
        self.parse_assign_tail(e)
    }

    fn parse_yield(&mut self) -> PResult<Expr> {
        if self.ctx.in_params {
            return Err(Fail::early("yield expression in formal parameters"));
        }
        self.next()?; // yield
        if self.tok.is_punct(P::Star) && !self.tok.newline_before {
            self.next()?;
            let arg = self.parse_assignment(false)?;
            return Ok(Expr::Yield {
                arg: Some(Box::new(arg)),
                delegate: true,
            });
        }
        let arg = if !self.tok.newline_before && self.token_starts_expression() {
            Some(Box::new(self.parse_assignment(false)?))
        } else {
            None
        };
        Ok(Expr::Yield {
            arg,
            delegate: false,
        })
    }

    fn token_starts_expression(&self) -> bool {
        match &self.tok.kind {
            TokenKind::Num { .. }
            | TokenKind::Str { .. }
            | TokenKind::Template { .. }
            | TokenKind::Regex { .. } => true,
            TokenKind::Ident(n) => {
                !Parser::is_always_reserved(n)
                    || matches!(
                        n.as_str(),
                        "this"
                            | "true"
                            | "false"
                            | "null"
                            | "function"
                            | "class"
                            | "new"
                            | "typeof"
                            | "void"
                            | "delete"
                            | "super"
                            | "import"
                    )
            }
            TokenKind::PrivateIdent(_) => true,
            TokenKind::Punct(p) => matches!(
                p,
                P::LParen
                    | P::LBracket
                    | P::LBrace
                    | P::Plus
                    | P::Minus
                    | P::Bang
                    | P::Tilde
                    | P::PlusPlus
                    | P::MinusMinus
                    | P::Slash
                    | P::SlashEq
            ),
            _ => false,
        }
    }

    fn parse_private_ref_operand(&mut self) -> PResult<Expr> {
        let name = match &self.tok.kind {
            TokenKind::PrivateIdent(n) => n.clone(),
            _ => unreachable!(),
        };
        let pos = self.tok.start;
        self.private_refs.push((name.clone(), pos));
        self.next()?;
        Ok(Expr::PrivateRef(name))
    }

    // ---- assignment / conditional / binary tails ------------------------

    pub fn parse_expr_tails(&mut self, base: Expr) -> PResult<Expr> {
        let e = self.parse_chain_from(base)?;
        let e = self.parse_postfix_tail(e)?;
        let e = self.parse_binary_from(e, 0)?;
        let e = self.parse_cond_from(e)?;
        self.parse_assign_tail(e)
    }

    fn parse_assign_tail(&mut self, e: Expr) -> PResult<Expr> {
        let op: &'static str = match &self.tok.kind {
            TokenKind::Punct(P::Eq) => "=",
            TokenKind::Punct(P::PlusEq) => "+=",
            TokenKind::Punct(P::MinusEq) => "-=",
            TokenKind::Punct(P::StarEq) => "*=",
            TokenKind::Punct(P::SlashEq) => "/=",
            TokenKind::Punct(P::PercentEq) => "%=",
            TokenKind::Punct(P::StarStarEq) => "**=",
            TokenKind::Punct(P::ShlEq) => "<<=",
            TokenKind::Punct(P::ShrEq) => ">>=",
            TokenKind::Punct(P::UShrEq) => ">>>=",
            TokenKind::Punct(P::AmpEq) => "&=",
            TokenKind::Punct(P::PipeEq) => "|=",
            TokenKind::Punct(P::CaretEq) => "^=",
            TokenKind::Punct(P::AmpAmpEq) => "&&=",
            TokenKind::Punct(P::PipePipeEq) => "||=",
            TokenKind::Punct(P::QuestionQuestionEq) => "??=",
            _ => return Ok(e),
        };
        if Self::is_plain_call(&e) {
            // Spec: early error (AssignmentTargetType is invalid). Web
            // reality (V8/JSC): parses, throws ReferenceError at runtime —
            // but only for a top-level call target, not nested in patterns.
            return Err(Fail::unsupported(
                "engine-divergent call-expression assignment target",
            ));
        }
        let target = if op == "=" {
            let t = self.expr_to_assign_target(e, true)?;
            // A successful conversion legitimizes cover-only forms in the LHS.
            self.pending = Pending::default();
            t
        } else {
            self.expr_to_assign_target(e, false)?
        };
        self.next()?;
        let value = self.parse_assignment(false)?;
        Ok(Expr::Assign {
            op,
            target: Box::new(target),
            value: Box::new(value),
        })
    }

    fn parse_cond_from(&mut self, e: Expr) -> PResult<Expr> {
        if !self.tok.is_punct(P::Question) {
            return Ok(e);
        }
        self.next()?;
        let saved_no_in = self.ctx.no_in;
        self.ctx.no_in = false;
        let cons = self.parse_assignment(false);
        self.ctx.no_in = saved_no_in;
        let cons = cons?;
        self.expect_punct(P::Colon, "':' in conditional expression")?;
        let alt = self.parse_assignment(false)?;
        Ok(Expr::Cond {
            test: Box::new(e),
            cons: Box::new(cons),
            alt: Box::new(alt),
        })
    }

    /// Operator table: (text, precedence, right_assoc).
    fn binary_op_of(&self) -> Option<(&'static str, u8, bool)> {
        match &self.tok.kind {
            TokenKind::Punct(p) => Some(match p {
                P::QuestionQuestion => ("??", 1, false),
                P::PipePipe => ("||", 2, false),
                P::AmpAmp => ("&&", 3, false),
                P::Pipe => ("|", 4, false),
                P::Caret => ("^", 5, false),
                P::Amp => ("&", 6, false),
                P::EqEq => ("==", 7, false),
                P::NotEq => ("!=", 7, false),
                P::EqEqEq => ("===", 7, false),
                P::NotEqEq => ("!==", 7, false),
                P::Lt => ("<", 8, false),
                P::Gt => (">", 8, false),
                P::Le => ("<=", 8, false),
                P::Ge => (">=", 8, false),
                P::Shl => ("<<", 9, false),
                P::Shr => (">>", 9, false),
                P::UShr => (">>>", 9, false),
                P::Plus => ("+", 10, false),
                P::Minus => ("-", 10, false),
                P::Star => ("*", 11, false),
                P::Slash => ("/", 11, false),
                P::Percent => ("%", 11, false),
                P::StarStar => ("**", 12, true),
                _ => return None,
            }),
            TokenKind::Ident(_) => {
                if self.tok.is_kw("instanceof") {
                    Some(("instanceof", 8, false))
                } else if self.tok.is_kw("in") {
                    Some(("in", 8, false))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn parse_binary_from(&mut self, mut left: Expr, min_prec: u8) -> PResult<Expr> {
        loop {
            let (op, prec, right_assoc) = match self.binary_op_of() {
                Some(x) => x,
                None => break,
            };
            if op == "in" && self.ctx.no_in {
                break;
            }
            if prec < min_prec {
                break;
            }
            if op == "**" && matches!(left, Expr::Unary { .. } | Expr::Await(_)) {
                return Err(Fail::early(
                    "unparenthesized unary expression cannot be the base of '**'",
                ));
            }
            self.next()?;
            let operand = if matches!(self.tok.kind, TokenKind::PrivateIdent(_)) {
                self.parse_private_ref_operand()?
            } else {
                self.parse_unary()?
            };
            let next_min = if right_assoc { prec } else { prec + 1 };
            let right = self.parse_binary_from(operand, next_min)?;
            if matches!(right, Expr::PrivateRef(_)) {
                return Err(Fail::early(
                    "private name must be the left operand of 'in'",
                ));
            }
            if matches!(left, Expr::PrivateRef(_)) && op != "in" {
                return Err(Fail::early(
                    "private name must be the left operand of 'in'",
                ));
            }
            left = match op {
                "&&" | "||" | "??" => {
                    if op == "??" && (Self::is_and_or(&left) || Self::is_and_or(&right)) {
                        return Err(Fail::early(
                            "'??' cannot be mixed with '&&'/'||' without parentheses",
                        ));
                    }
                    Expr::Logical {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                }
                _ => Expr::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
            };
        }
        Ok(left)
    }

    fn is_and_or(e: &Expr) -> bool {
        matches!(e, Expr::Logical { op, .. } if *op == "&&" || *op == "||")
    }

    // ---- unary / update -------------------------------------------------

    fn parse_unary(&mut self) -> PResult<Expr> {
        let g = self.enter()?;
        let r = self.parse_unary_inner();
        self.leave(g);
        r
    }

    fn parse_unary_inner(&mut self) -> PResult<Expr> {
        if let TokenKind::Ident(_) = &self.tok.kind {
            if self.tok.is_kw("delete") || self.tok.is_kw("void") || self.tok.is_kw("typeof") {
                let op: &'static str = if self.tok.is_kw("delete") {
                    "delete"
                } else if self.tok.is_kw("void") {
                    "void"
                } else {
                    "typeof"
                };
                self.next()?;
                let arg = self.parse_unary()?;
                if op == "delete" {
                    let inner = Self::unwrap_parens(&arg);
                    if self.ctx.strict && matches!(inner, Expr::Ident(_)) {
                        return Err(Fail::early(
                            "delete of an unqualified identifier in strict mode",
                        ));
                    }
                    if let Expr::Member { prop, .. } = inner {
                        if matches!(**prop, PropKey::Private(_)) {
                            return Err(Fail::early("private members may not be deleted"));
                        }
                    }
                }
                return Ok(Expr::Unary {
                    op,
                    arg: Box::new(arg),
                });
            }
            if self.tok.is_kw("await") && (self.ctx.await_expr || self.ctx.static_block) {
                if self.ctx.static_block {
                    return Err(Fail::early("await is not allowed in class static blocks"));
                }
                if self.ctx.in_params {
                    return Err(Fail::early("await expression in formal parameters"));
                }
                self.next()?;
                let arg = self.parse_unary()?;
                return Ok(Expr::Await(Box::new(arg)));
            }
        }
        match &self.tok.kind {
            TokenKind::Punct(P::Plus) => self.parse_simple_unary("+"),
            TokenKind::Punct(P::Minus) => self.parse_simple_unary("-"),
            TokenKind::Punct(P::Tilde) => self.parse_simple_unary("~"),
            TokenKind::Punct(P::Bang) => self.parse_simple_unary("!"),
            TokenKind::Punct(P::PlusPlus) | TokenKind::Punct(P::MinusMinus) => {
                let op: &'static str = if self.tok.is_punct(P::PlusPlus) {
                    "++"
                } else {
                    "--"
                };
                self.next()?;
                let arg = self.parse_unary()?;
                self.check_update_target(&arg)?;
                Ok(Expr::Update {
                    op,
                    prefix: true,
                    arg: Box::new(arg),
                })
            }
            _ => {
                let e = self.parse_lhs_expression()?;
                self.parse_postfix_tail(e)
            }
        }
    }

    fn parse_simple_unary(&mut self, op: &'static str) -> PResult<Expr> {
        self.next()?;
        let arg = self.parse_unary()?;
        Ok(Expr::Unary {
            op,
            arg: Box::new(arg),
        })
    }

    fn parse_postfix_tail(&mut self, e: Expr) -> PResult<Expr> {
        if (self.tok.is_punct(P::PlusPlus) || self.tok.is_punct(P::MinusMinus))
            && !self.tok.newline_before
        {
            self.check_update_target(&e)?;
            let op: &'static str = if self.tok.is_punct(P::PlusPlus) {
                "++"
            } else {
                "--"
            };
            self.next()?;
            return Ok(Expr::Update {
                op,
                prefix: false,
                arg: Box::new(e),
            });
        }
        Ok(e)
    }

    fn unwrap_parens(e: &Expr) -> &Expr {
        let mut cur = e;
        while let Expr::Paren(inner) = cur {
            cur = inner;
        }
        cur
    }

    /// A non-optional call expression (possibly parenthesized) — the
    /// engine-divergent assignment-target class.
    pub fn is_plain_call(e: &Expr) -> bool {
        matches!(
            Self::unwrap_parens(e),
            Expr::Call {
                optional: false,
                in_chain: false,
                ..
            }
        )
    }

    fn check_update_target(&self, e: &Expr) -> PResult<()> {
        if Self::is_plain_call(e) {
            return Err(Fail::unsupported(
                "engine-divergent call-expression update target",
            ));
        }
        match Self::unwrap_parens(e) {
            Expr::Ident(n) => {
                if self.ctx.strict && (n == "eval" || n == "arguments") {
                    return Err(Fail::early(format!(
                        "cannot update '{n}' in strict mode"
                    )));
                }
                Ok(())
            }
            Expr::Member {
                optional: false,
                in_chain: false,
                ..
            }
            | Expr::SuperProp(_) => Ok(()),
            _ => Err(Fail::early("invalid increment/decrement target")),
        }
    }

    // ---- LeftHandSideExpression -----------------------------------------

    pub fn parse_lhs_expression(&mut self) -> PResult<Expr> {
        let g = self.enter()?;
        let r = (|| {
            let base = if self.tok.is_kw("new") {
                self.parse_new_expr()?
            } else {
                self.parse_primary()?
            };
            self.parse_chain_from(base)
        })();
        self.leave(g);
        r
    }

    fn parse_new_expr(&mut self) -> PResult<Expr> {
        let g = self.enter()?;
        let r = self.parse_new_expr_inner();
        self.leave(g);
        r
    }

    fn parse_new_expr_inner(&mut self) -> PResult<Expr> {
        self.next()?; // new
        if self.tok.is_punct(P::Dot) {
            self.next()?;
            if !self.tok.is_kw("target") {
                return Err(Fail::early("expected 'target' after 'new.'"));
            }
            if !self.ctx.new_target_ok {
                return Err(Fail::early("new.target outside of function"));
            }
            self.next()?;
            return Ok(Expr::NewTarget);
        }
        let callee = self.parse_new_callee()?;
        let args = if self.tok.is_punct(P::LParen) {
            self.parse_args(false)?
        } else {
            Vec::new()
        };
        Ok(Expr::New {
            callee: Box::new(callee),
            args,
        })
    }

    /// MemberExpression restricted for a new callee: member accesses and
    /// tagged templates, but no calls and no optional chains.
    fn parse_new_callee(&mut self) -> PResult<Expr> {
        if self.tok.is_kw("import") {
            // `new import.meta` is legal (import.meta is a MetaProperty, i.e. a
            // MemberExpression); `new import(…)` is not (ImportCall is a
            // CallExpression). Only the meta-property form (module goal) is a
            // valid new callee — fall through to parse_primary for it.
            let p = self.peek()?;
            if !(p.is_punct(P::Dot) && self.ctx.in_module) {
                return Err(Fail::early("cannot use 'new' with import()"));
            }
        }
        let mut base = if self.tok.is_kw("new") {
            self.parse_new_expr()?
        } else {
            self.parse_primary()?
        };
        loop {
            match &self.tok.kind {
                TokenKind::Punct(P::Dot) => {
                    self.next()?;
                    base = self.parse_member_prop(base, false, false)?;
                }
                TokenKind::Punct(P::LBracket) => {
                    self.next()?;
                    let saved_no_in = self.ctx.no_in;
                    self.ctx.no_in = false;
                    let idx = self.parse_expression();
                    self.ctx.no_in = saved_no_in;
                    let idx = idx?;
                    self.expect_punct(P::RBracket, "']'")?;
                    base = Expr::Member {
                        obj: Box::new(base),
                        prop: Box::new(PropKey::Computed(Box::new(idx))),
                        optional: false,
                        in_chain: false,
                    };
                }
                TokenKind::Punct(P::QuestionDot) => {
                    return Err(Fail::early("optional chain in new callee"));
                }
                TokenKind::Template {
                    kind: TplKind::NoSub | TplKind::Head,
                    ..
                } => {
                    base = self.parse_tagged_template(base)?;
                }
                _ => break,
            }
        }
        Ok(base)
    }

    fn parse_member_prop(&mut self, obj: Expr, optional: bool, in_chain: bool) -> PResult<Expr> {
        let key = match &self.tok.kind {
            TokenKind::Ident(n) => PropKey::Ident(n.clone()),
            TokenKind::PrivateIdent(n) => {
                let n = n.clone();
                self.private_refs.push((n.clone(), self.tok.start));
                PropKey::Private(n)
            }
            _ => return Err(Fail::early("expected property name after '.'")),
        };
        self.next()?;
        Ok(Expr::Member {
            obj: Box::new(obj),
            prop: Box::new(key),
            optional,
            in_chain,
        })
    }

    fn parse_chain_from(&mut self, mut e: Expr) -> PResult<Expr> {
        let mut in_chain = matches!(
            e,
            Expr::Member { in_chain: true, .. } | Expr::Call { in_chain: true, .. }
        );
        loop {
            match &self.tok.kind {
                TokenKind::Punct(P::Dot) => {
                    self.next()?;
                    e = self.parse_member_prop(e, false, in_chain)?;
                }
                TokenKind::Punct(P::LBracket) => {
                    self.next()?;
                    let saved_no_in = self.ctx.no_in;
                    self.ctx.no_in = false;
                    let idx = self.parse_expression();
                    self.ctx.no_in = saved_no_in;
                    let idx = idx?;
                    self.expect_punct(P::RBracket, "']'")?;
                    e = Expr::Member {
                        obj: Box::new(e),
                        prop: Box::new(PropKey::Computed(Box::new(idx))),
                        optional: false,
                        in_chain,
                    };
                }
                TokenKind::Punct(P::LParen) => {
                    let args = self.parse_args(false)?;
                    e = Expr::Call {
                        callee: Box::new(e),
                        args,
                        optional: false,
                        in_chain,
                    };
                }
                TokenKind::Punct(P::QuestionDot) => {
                    in_chain = true;
                    self.next()?;
                    match &self.tok.kind {
                        TokenKind::Punct(P::LParen) => {
                            let args = self.parse_args(false)?;
                            e = Expr::Call {
                                callee: Box::new(e),
                                args,
                                optional: true,
                                in_chain: true,
                            };
                        }
                        TokenKind::Punct(P::LBracket) => {
                            self.next()?;
                            let saved_no_in = self.ctx.no_in;
                            self.ctx.no_in = false;
                            let idx = self.parse_expression();
                            self.ctx.no_in = saved_no_in;
                            let idx = idx?;
                            self.expect_punct(P::RBracket, "']'")?;
                            e = Expr::Member {
                                obj: Box::new(e),
                                prop: Box::new(PropKey::Computed(Box::new(idx))),
                                optional: true,
                                in_chain: true,
                            };
                        }
                        TokenKind::Ident(_) | TokenKind::PrivateIdent(_) => {
                            e = self.parse_member_prop(e, true, true)?;
                        }
                        TokenKind::Template { .. } => {
                            return Err(Fail::early(
                                "tagged template in optional chain",
                            ));
                        }
                        _ => return Err(Fail::early("unexpected token after '?.'")),
                    }
                }
                TokenKind::Template {
                    kind: TplKind::NoSub | TplKind::Head,
                    ..
                } => {
                    if in_chain {
                        return Err(Fail::early("tagged template in optional chain"));
                    }
                    e = self.parse_tagged_template(e)?;
                }
                _ => break,
            }
        }
        Ok(e)
    }

    pub fn parse_args(&mut self, allow_cover: bool) -> PResult<Vec<Arg>> {
        self.expect_punct(P::LParen, "'('")?;
        let saved_no_in = self.ctx.no_in;
        self.ctx.no_in = false;
        let r = self.parse_args_inner(allow_cover);
        self.ctx.no_in = saved_no_in;
        r
    }

    fn parse_args_inner(&mut self, allow_cover: bool) -> PResult<Vec<Arg>> {
        let mut args = Vec::new();
        loop {
            if self.tok.is_punct(P::RParen) {
                break;
            }
            if self.eat_punct(P::Ellipsis)? {
                args.push(Arg::Spread(self.parse_assignment(allow_cover)?));
            } else {
                args.push(Arg::Expr(self.parse_assignment(allow_cover)?));
            }
            if self.tok.is_punct(P::RParen) {
                break;
            }
            self.expect_punct(P::Comma, "',' between arguments")?;
        }
        self.expect_punct(P::RParen, "')'")?;
        Ok(args)
    }

    // ---- arrows & the paren cover grammar -------------------------------

    /// `Ident => …` (and `async Ident => …` with async already consumed).
    fn parse_arrow_single_ident(&mut self, is_async: bool) -> PResult<Expr> {
        let name = match &self.tok.kind {
            TokenKind::Ident(n) => n.clone(),
            _ => return Err(Fail::early("expected arrow parameter")),
        };
        let saved_ctx = self.ctx;
        self.ctx.in_params = true;
        if is_async {
            self.ctx.await_expr = true;
        }
        let check = self.check_binding_ident(&name);
        self.ctx = saved_ctx;
        check?;
        self.next()?; // param
        if !self.tok.is_punct(P::Arrow) || self.tok.newline_before {
            return Err(Fail::early("expected '=>' after arrow parameter"));
        }
        self.next()?; // =>
        self.push_scope(ScopeKind::FnBody);
        self.scopes
            .last_mut()
            .expect("scope")
            .var_names
            .insert(name.clone(), ());
        let info = ParamInfo {
            params: vec![Pat::Ident(name.clone())],
            names: vec![name],
            simple: true,
            has_dup: false,
            has_rest: false,
        };
        let r = self.parse_arrow_body(info, is_async);
        self.pop_scope();
        r
    }

    /// Cover grammar for `( … )` at AssignmentExpression level: lenient
    /// first pass, then a true reparse of the span as ArrowFormalParameters
    /// when `=>` follows, else a parenthesized expression + tails.
    fn parse_paren_or_arrow(&mut self) -> PResult<Expr> {
        let lparen_start = self.tok.start;
        let refs_mark = self.private_refs.len();
        let saved_no_in = self.ctx.no_in;
        self.ctx.no_in = false;
        let scan = self.scan_paren_cover();
        self.ctx.no_in = saved_no_in;
        let (items, cover_only) = scan?;
        if self.tok.is_punct(P::Arrow) && !self.tok.newline_before {
            self.private_refs.truncate(refs_mark);
            self.pending = Pending::default();
            return self.parse_arrow_with_reparsed_params(lparen_start, false);
        }
        if cover_only {
            return Err(Fail::early(
                "parenthesized expression cannot be empty or contain rest/trailing comma",
            ));
        }
        let mut items = items;
        let inner = if items.len() == 1 {
            items.pop().expect("one item")
        } else {
            Expr::Seq(items)
        };
        let base = Expr::Paren(Box::new(inner));
        self.parse_expr_tails(base)
    }

    /// Lenient scan of `( … )` contents. Returns (items, cover_only).
    fn scan_paren_cover(&mut self) -> PResult<(Vec<Expr>, bool)> {
        self.next()?; // (
        let mut items = Vec::new();
        let mut cover_only = false;
        if self.tok.is_punct(P::RParen) {
            cover_only = true;
            self.next()?;
            return Ok((items, cover_only));
        }
        loop {
            if self.eat_punct(P::Ellipsis)? {
                cover_only = true;
                let _ = self.parse_assignment(true)?;
                if self.tok.is_punct(P::Comma) {
                    return Err(Fail::early("rest parameter must be last"));
                }
                break;
            }
            items.push(self.parse_assignment(true)?);
            if self.eat_punct(P::Comma)? {
                if self.tok.is_punct(P::RParen) {
                    cover_only = true;
                    break;
                }
                continue;
            }
            break;
        }
        self.expect_punct(P::RParen, "')'")?;
        Ok((items, cover_only))
    }

    /// Seek back to `(` and reparse the span as ArrowFormalParameters, then
    /// parse the arrow body. Current token must be `=>`.
    fn parse_arrow_with_reparsed_params(
        &mut self,
        lparen_start: usize,
        is_async: bool,
    ) -> PResult<Expr> {
        self.lx.seek(lparen_start);
        self.next()?; // (
        let saved_ctx = self.ctx;
        self.ctx.in_params = true;
        if is_async {
            self.ctx.await_expr = true;
        }
        self.push_scope(ScopeKind::FnBody);
        let r = (|| {
            self.expect_punct(P::LParen, "'('")?;
            self.parse_formal_params(true)
        })();
        self.ctx = saved_ctx;
        let info = match r {
            Ok(i) => i,
            Err(e) => {
                self.pop_scope();
                return Err(e);
            }
        };
        if !self.tok.is_punct(P::Arrow) {
            self.pop_scope();
            return Err(Fail::early("arrow parameter reparse mismatch"));
        }
        self.next()?; // =>
        let body = self.parse_arrow_body(info, is_async);
        self.pop_scope();
        body
    }

    /// Arrow body with the arrow's context: yield never an expression,
    /// await per async-ness; new.target/super/no_arguments inherited.
    fn parse_arrow_body(&mut self, info: ParamInfo, is_async: bool) -> PResult<Expr> {
        let saved_ctx = self.ctx;
        let saved_barrier = self.label_barrier;
        self.label_barrier = self.labels.len();
        self.ctx.yield_expr = false;
        self.ctx.await_expr = is_async;
        self.ctx.in_function = true;
        self.ctx.in_iteration = false;
        self.ctx.in_switch = false;
        self.ctx.in_params = false;
        // The static-block await ban does not descend into arrow bodies
        // (Contains stops at arrow boundaries for `await`); the arguments
        // ban DOES (ContainsArguments descends through arrows).
        self.ctx.static_block = false;
        // new_target_ok, super_prop_ok, super_call_ok, no_arguments:
        // inherited (arrows are transparent to them).
        let r = self.parse_arrow_body_inner(info, is_async);
        self.label_barrier = saved_barrier;
        self.ctx = saved_ctx;
        r
    }

    fn parse_arrow_body_inner(&mut self, info: ParamInfo, is_async: bool) -> PResult<Expr> {
        if self.tok.is_punct(P::LBrace) {
            self.next()?;
            let saved_no_in = self.ctx.no_in;
            self.ctx.no_in = false;
            let body = self.parse_body_statements(Some(P::RBrace), info.simple);
            self.ctx.no_in = saved_no_in;
            let (body, became_strict) = body?;
            self.expect_punct(P::RBrace, "'}' after arrow body")?;
            if became_strict {
                self.revalidate_strict_params(&info, None)?;
            }
            return Ok(Expr::Arrow(Func {
                name: None,
                params: info.params,
                body,
                expr_body: None,
                is_async,
                is_gen: false,
                is_arrow: true,
                strict: self.ctx.strict,
            }));
        }
        let e = self.parse_assignment(false)?;
        Ok(Expr::Arrow(Func {
            name: None,
            params: info.params,
            body: Vec::new(),
            expr_body: Some(Box::new(e)),
            is_async,
            is_gen: false,
            is_arrow: true,
            strict: self.ctx.strict,
        }))
    }

    /// `async ( … )` — CoverCallExpressionAndAsyncArrowHead.
    fn parse_async_paren(&mut self) -> PResult<Expr> {
        self.next()?; // async
        let lparen_start = self.tok.start;
        let refs_mark = self.private_refs.len();
        let args = self.parse_args(true)?;
        if self.tok.is_punct(P::Arrow) && !self.tok.newline_before {
            self.private_refs.truncate(refs_mark);
            self.pending = Pending::default();
            return self.parse_arrow_with_reparsed_params(lparen_start, true);
        }
        let base = Expr::Call {
            callee: Box::new(Expr::Ident("async".to_string())),
            args,
            optional: false,
            in_chain: false,
        };
        self.parse_expr_tails(base)
    }

    // ---- formal parameters & binding patterns ---------------------------

    /// Parses up to and including the closing `)`. Requires the caller to
    /// have consumed `(` and pushed the function scope.
    pub fn parse_formal_params(&mut self, unique: bool) -> PResult<ParamInfo> {
        let saved_no_in = self.ctx.no_in;
        self.ctx.no_in = false;
        let saved_in_params = self.ctx.in_params;
        self.ctx.in_params = true;
        let r = self.parse_formal_params_inner(unique);
        self.ctx.no_in = saved_no_in;
        self.ctx.in_params = saved_in_params;
        r
    }

    fn parse_formal_params_inner(&mut self, unique: bool) -> PResult<ParamInfo> {
        let mut params = Vec::new();
        let mut names: Vec<String> = Vec::new();
        let mut simple = true;
        let mut has_rest = false;
        loop {
            if self.tok.is_punct(P::RParen) {
                break;
            }
            if self.eat_punct(P::Ellipsis)? {
                has_rest = true;
                simple = false;
                let pat = self.parse_binding_target_collect(BindTarget::Param, &mut names)?;
                if self.tok.is_punct(P::Eq) {
                    return Err(Fail::early("rest parameter cannot have a default"));
                }
                if self.tok.is_punct(P::Comma) {
                    return Err(Fail::early("rest parameter must be last"));
                }
                params.push(Pat::Rest(Box::new(pat)));
                break;
            }
            let is_ident = matches!(self.tok.kind, TokenKind::Ident(_));
            let mut pat = self.parse_binding_target_collect(BindTarget::Param, &mut names)?;
            if !is_ident {
                simple = false;
            }
            if self.eat_punct(P::Eq)? {
                simple = false;
                let init = self.parse_assignment(false)?;
                pat = Pat::Default(Box::new(pat), Box::new(init));
            }
            params.push(pat);
            if self.tok.is_punct(P::RParen) {
                break;
            }
            self.expect_punct(P::Comma, "',' between parameters")?;
        }
        self.expect_punct(P::RParen, "')' after parameters")?;
        let mut sorted = names.clone();
        sorted.sort();
        let has_dup = sorted.windows(2).any(|w| w[0] == w[1]);
        if has_dup && (unique || self.ctx.strict || !simple) {
            return Err(Fail::early("duplicate parameter names not allowed here"));
        }
        Ok(ParamInfo {
            params,
            names,
            simple,
            has_dup,
            has_rest,
        })
    }

    pub fn parse_binding_target(&mut self, target: BindTarget) -> PResult<Pat> {
        let mut names = Vec::new();
        self.parse_binding_target_collect(target, &mut names)
    }

    fn parse_binding_target_collect(
        &mut self,
        target: BindTarget,
        names: &mut Vec<String>,
    ) -> PResult<Pat> {
        let g = self.enter()?;
        let r = self.parse_binding_target_inner(target, names);
        self.leave(g);
        r
    }

    fn declare_binding(
        &mut self,
        name: &str,
        target: BindTarget,
        names: &mut Vec<String>,
    ) -> PResult<()> {
        self.check_binding_ident(name)?;
        match target {
            BindTarget::Var => self.declare_var(name)?,
            BindTarget::LetConst => {
                if name == "let" {
                    return Err(Fail::early(
                        "'let' may not be a lexically bound name",
                    ));
                }
                self.declare_lexical(name, crate::parser::LexKind::LetConst)?;
            }
            BindTarget::Param => {
                names.push(name.to_string());
                if let Some(s) = self.scopes.last_mut() {
                    s.var_names.insert(name.to_string(), ());
                }
            }
            BindTarget::CatchParam => {
                self.declare_lexical(name, crate::parser::LexKind::CatchParam)?;
            }
        }
        Ok(())
    }

    fn parse_binding_target_inner(
        &mut self,
        target: BindTarget,
        names: &mut Vec<String>,
    ) -> PResult<Pat> {
        match &self.tok.kind {
            TokenKind::Ident(n) => {
                let n = n.clone();
                self.declare_binding(&n, target, names)?;
                self.next()?;
                Ok(Pat::Ident(n))
            }
            TokenKind::Punct(P::LBracket) => {
                self.next()?;
                let mut elems: Vec<Option<Pat>> = Vec::new();
                let mut rest = None;
                loop {
                    if self.tok.is_punct(P::RBracket) {
                        break;
                    }
                    if self.eat_punct(P::Comma)? {
                        elems.push(None);
                        continue;
                    }
                    if self.eat_punct(P::Ellipsis)? {
                        let inner = self.parse_binding_target_collect(target, names)?;
                        if self.tok.is_punct(P::Eq) {
                            return Err(Fail::early("rest element cannot have a default"));
                        }
                        if self.tok.is_punct(P::Comma) {
                            return Err(Fail::early("rest element must be last"));
                        }
                        rest = Some(Box::new(inner));
                        break;
                    }
                    let mut el = self.parse_binding_target_collect(target, names)?;
                    if self.eat_punct(P::Eq)? {
                        let saved_no_in = self.ctx.no_in;
                        self.ctx.no_in = false;
                        let init = self.parse_assignment(false);
                        self.ctx.no_in = saved_no_in;
                        el = Pat::Default(Box::new(el), Box::new(init?));
                    }
                    elems.push(Some(el));
                    if self.tok.is_punct(P::RBracket) {
                        break;
                    }
                    self.expect_punct(P::Comma, "',' in array pattern")?;
                }
                self.expect_punct(P::RBracket, "']' after array pattern")?;
                Ok(Pat::Array { elems, rest })
            }
            TokenKind::Punct(P::LBrace) => {
                self.next()?;
                let mut props = Vec::new();
                let mut rest = None;
                loop {
                    if self.tok.is_punct(P::RBrace) {
                        break;
                    }
                    if self.eat_punct(P::Ellipsis)? {
                        match &self.tok.kind {
                            TokenKind::Ident(n) => {
                                let n = n.clone();
                                self.declare_binding(&n, target, names)?;
                                self.next()?;
                                rest = Some(Box::new(Pat::Ident(n)));
                            }
                            _ => {
                                return Err(Fail::early(
                                    "binding rest property must be an identifier",
                                ))
                            }
                        }
                        if self.tok.is_punct(P::Comma) {
                            return Err(Fail::early("rest property must be last"));
                        }
                        break;
                    }
                    let key_is_plain_ident = matches!(self.tok.kind, TokenKind::Ident(_));
                    let key = self.parse_property_name()?;
                    if matches!(key, PropKey::Private(_)) {
                        return Err(Fail::early("private name in binding pattern"));
                    }
                    let value = if self.eat_punct(P::Colon)? {
                        let mut v = self.parse_binding_target_collect(target, names)?;
                        if self.eat_punct(P::Eq)? {
                            let saved_no_in = self.ctx.no_in;
                            self.ctx.no_in = false;
                            let init = self.parse_assignment(false);
                            self.ctx.no_in = saved_no_in;
                            v = Pat::Default(Box::new(v), Box::new(init?));
                        }
                        v
                    } else if key_is_plain_ident {
                        let n = match &key {
                            PropKey::Ident(n) => n.clone(),
                            _ => unreachable!(),
                        };
                        self.declare_binding(&n, target, names)?;
                        let mut v = Pat::Ident(n);
                        if self.eat_punct(P::Eq)? {
                            let saved_no_in = self.ctx.no_in;
                            self.ctx.no_in = false;
                            let init = self.parse_assignment(false);
                            self.ctx.no_in = saved_no_in;
                            v = Pat::Default(Box::new(v), Box::new(init?));
                        }
                        v
                    } else {
                        return Err(Fail::early("expected ':' in object pattern"));
                    };
                    props.push(ObjPatProp { key, value });
                    if self.tok.is_punct(P::RBrace) {
                        break;
                    }
                    self.expect_punct(P::Comma, "',' in object pattern")?;
                }
                self.expect_punct(P::RBrace, "'}' after object pattern")?;
                Ok(Pat::Object { props, rest })
            }
            _ => Err(Fail::early("invalid binding pattern")),
        }
    }

    // ---- assignment-target conversion -----------------------------------

    pub fn expr_to_assign_target(&mut self, e: Expr, allow_pattern: bool) -> PResult<Pat> {
        let g = self.enter()?;
        let r = self.expr_to_assign_target_inner(e, allow_pattern);
        self.leave(g);
        r
    }

    fn expr_to_assign_target_inner(&mut self, e: Expr, allow_pattern: bool) -> PResult<Pat> {
        match e {
            Expr::Ident(n) => {
                if self.ctx.strict && (n == "eval" || n == "arguments") {
                    return Err(Fail::early(format!(
                        "cannot assign to '{n}' in strict mode"
                    )));
                }
                Ok(Pat::Ident(n))
            }
            Expr::Member {
                optional, in_chain, ..
            } => {
                if optional || in_chain {
                    return Err(Fail::early("optional chain is not a valid assignment target"));
                }
                Ok(Pat::Expr(Box::new(e)))
            }
            Expr::SuperProp(_) => Ok(Pat::Expr(Box::new(e))),
            Expr::Paren(inner) => self.expr_to_assign_target(*inner, false),
            Expr::Array {
                elems,
                trailing_comma,
            } if allow_pattern => {
                let n = elems.len();
                let mut out: Vec<Option<Pat>> = Vec::new();
                let mut rest: Option<Box<Pat>> = None;
                for (i, el) in elems.into_iter().enumerate() {
                    match el {
                        None => out.push(None),
                        Some(Arg::Expr(x)) => {
                            out.push(Some(self.elem_to_target(x)?));
                        }
                        Some(Arg::Spread(x)) => {
                            if i + 1 != n || trailing_comma {
                                return Err(Fail::early(
                                    "rest element must be last in assignment pattern",
                                ));
                            }
                            if matches!(x, Expr::Assign { .. }) {
                                return Err(Fail::early("rest element cannot have a default"));
                            }
                            rest = Some(Box::new(self.expr_to_assign_target(x, true)?));
                        }
                    }
                }
                Ok(Pat::Array { elems: out, rest })
            }
            Expr::Object(props) if allow_pattern => {
                let n = props.len();
                let mut out = Vec::new();
                let mut rest: Option<Box<Pat>> = None;
                for (i, prop) in props.into_iter().enumerate() {
                    match prop {
                        ObjProp::Shorthand(name) => {
                            if self.ctx.strict && (name == "eval" || name == "arguments") {
                                return Err(Fail::early(format!(
                                    "cannot assign to '{name}' in strict mode"
                                )));
                            }
                            out.push(ObjPatProp {
                                key: PropKey::Ident(name.clone()),
                                value: Pat::Ident(name),
                            });
                        }
                        ObjProp::CoverInit(name, default) => {
                            if self.ctx.strict && (name == "eval" || name == "arguments") {
                                return Err(Fail::early(format!(
                                    "cannot assign to '{name}' in strict mode"
                                )));
                            }
                            out.push(ObjPatProp {
                                key: PropKey::Ident(name.clone()),
                                value: Pat::Default(Box::new(Pat::Ident(name)), default),
                            });
                        }
                        ObjProp::KeyValue { key, value } => {
                            let value = self.elem_to_target(value)?;
                            out.push(ObjPatProp { key, value });
                        }
                        ObjProp::Method { .. } => {
                            return Err(Fail::early(
                                "method is not a valid assignment-pattern property",
                            ))
                        }
                        ObjProp::Spread(x) => {
                            if i + 1 != n {
                                return Err(Fail::early(
                                    "rest property must be last in assignment pattern",
                                ));
                            }
                            if matches!(x, Expr::Assign { .. }) {
                                return Err(Fail::early("rest property cannot have a default"));
                            }
                            rest = Some(Box::new(self.expr_to_assign_target(x, false)?));
                        }
                    }
                }
                Ok(Pat::Object { props: out, rest })
            }
            Expr::Assign {
                op: "=",
                target,
                value,
            } if allow_pattern => Ok(Pat::Default(target, value)),
            _ => Err(Fail::early("invalid assignment target")),
        }
    }

    /// Array/object pattern element: allows nested patterns and defaults.
    fn elem_to_target(&mut self, e: Expr) -> PResult<Pat> {
        match e {
            Expr::Assign {
                op: "=",
                target,
                value,
            } => Ok(Pat::Default(target, value)),
            other => self.expr_to_assign_target(other, true),
        }
    }

    // ---- primaries ------------------------------------------------------

    fn parse_primary(&mut self) -> PResult<Expr> {
        let g = self.enter()?;
        let r = self.parse_primary_inner();
        self.leave(g);
        r
    }

    fn parse_primary_inner(&mut self) -> PResult<Expr> {
        match &self.tok.kind {
            TokenKind::Num { raw, flags } => {
                if self.ctx.strict && flags.legacy_octal {
                    return Err(Fail::early("legacy octal literal in strict mode"));
                }
                if self.ctx.strict && flags.non_octal_decimal {
                    return Err(Fail::early(
                        "decimal literal with leading zero in strict mode",
                    ));
                }
                let raw = raw.clone();
                let bigint = flags.bigint;
                self.next()?;
                Ok(if bigint {
                    Expr::BigInt(raw)
                } else {
                    Expr::Num(raw)
                })
            }
            TokenKind::Str { raw, flags } => {
                if self.ctx.strict && flags.legacy_octal_escape {
                    return Err(Fail::early("octal escape sequence in strict mode"));
                }
                if self.ctx.strict && flags.non_octal_escape {
                    return Err(Fail::early("\\8 and \\9 escapes in strict mode"));
                }
                let e = Expr::Str {
                    raw: raw.clone(),
                    any_escape: flags.any_escape,
                    octal: flags.legacy_octal_escape || flags.non_octal_escape,
                };
                self.next()?;
                Ok(e)
            }
            TokenKind::Template {
                kind: TplKind::NoSub | TplKind::Head,
                ..
            } => {
                let (quasis, exprs) = self.parse_template_parts(false)?;
                Ok(Expr::Template { quasis, exprs })
            }
            TokenKind::Punct(P::Slash) | TokenKind::Punct(P::SlashEq) => {
                self.tok = self.lx.relex_regex(self.tok.start)?;
                let (pattern, flags) = match &self.tok.kind {
                    TokenKind::Regex { pattern, flags } => (pattern.clone(), flags.clone()),
                    _ => unreachable!(),
                };
                validate_regex(&pattern, &flags)?;
                self.next()?;
                Ok(Expr::Regex { pattern, flags })
            }
            TokenKind::Punct(P::LParen) => self.parse_paren_primary(),
            TokenKind::Punct(P::LBracket) => self.parse_array_literal(),
            TokenKind::Punct(P::LBrace) => self.parse_object_literal(),
            TokenKind::Ident(name) => {
                let name = name.clone();
                if !self.tok.had_escape {
                    match name.as_str() {
                        "this" => {
                            self.next()?;
                            return Ok(Expr::This);
                        }
                        "true" | "false" => {
                            let v = name == "true";
                            self.next()?;
                            return Ok(Expr::Bool(v));
                        }
                        "null" => {
                            self.next()?;
                            return Ok(Expr::Null);
                        }
                        "function" => return self.parse_function_expression(false),
                        "class" => return self.parse_class_expression(),
                        "async" => {
                            let p = self.peek()?;
                            if p.is_kw("function") && !p.newline_before {
                                return self.parse_function_expression(true);
                            }
                        }
                        "super" => return self.parse_super(),
                        "import" => return self.parse_import_expr(),
                        "new" => return self.parse_new_expr(),
                        _ => {}
                    }
                }
                self.check_ident_ref(&name)?;
                self.next()?;
                Ok(Expr::Ident(name))
            }
            TokenKind::PrivateIdent(_) => Err(Fail::early(
                "private name is only valid as the left operand of 'in' or after '.'",
            )),
            TokenKind::Eof => Err(Fail::early("unexpected end of input")),
            _ => Err(Fail::early("unexpected token in expression")),
        }
    }

    fn parse_super(&mut self) -> PResult<Expr> {
        self.next()?; // super
        match &self.tok.kind {
            TokenKind::Punct(P::Dot) => {
                if !self.ctx.super_prop_ok {
                    return Err(Fail::early("'super' property access outside of method"));
                }
                self.next()?;
                let key = match &self.tok.kind {
                    TokenKind::Ident(n) => PropKey::Ident(n.clone()),
                    TokenKind::PrivateIdent(_) => {
                        return Err(Fail::early("private member access on 'super'"))
                    }
                    _ => return Err(Fail::early("expected property name after 'super.'")),
                };
                self.next()?;
                Ok(Expr::SuperProp(Box::new(key)))
            }
            TokenKind::Punct(P::LBracket) => {
                if !self.ctx.super_prop_ok {
                    return Err(Fail::early("'super' property access outside of method"));
                }
                self.next()?;
                let saved_no_in = self.ctx.no_in;
                self.ctx.no_in = false;
                let idx = self.parse_expression();
                self.ctx.no_in = saved_no_in;
                let idx = idx?;
                self.expect_punct(P::RBracket, "']'")?;
                Ok(Expr::SuperProp(Box::new(PropKey::Computed(Box::new(idx)))))
            }
            TokenKind::Punct(P::LParen) => {
                if !self.ctx.super_call_ok {
                    return Err(Fail::early(
                        "'super' call outside of derived-class constructor",
                    ));
                }
                let args = self.parse_args(false)?;
                Ok(Expr::SuperCall(args))
            }
            _ => Err(Fail::early("unexpected 'super'")),
        }
    }

    fn parse_import_expr(&mut self) -> PResult<Expr> {
        self.next()?; // import
        match &self.tok.kind {
            TokenKind::Punct(P::LParen) => {
                self.next()?;
                let saved_no_in = self.ctx.no_in;
                self.ctx.no_in = false;
                let r = self.parse_import_args();
                self.ctx.no_in = saved_no_in;
                r
            }
            TokenKind::Punct(P::Dot) => {
                self.next()?;
                if self.tok.is_kw("meta") {
                    if self.ctx.in_module {
                        self.next()?; // meta
                        Ok(Expr::ImportMeta)
                    } else {
                        Err(Fail::early("import.meta is only valid in modules"))
                    }
                } else if self.tok.is_kw("source") {
                    // Source-phase imports: import.source(expr) is valid
                    // call syntax in scripts.
                    self.next()?;
                    if !self.tok.is_punct(P::LParen) {
                        return Err(Fail::early("expected '(' after import.source"));
                    }
                    self.next()?;
                    let saved_no_in = self.ctx.no_in;
                    self.ctx.no_in = false;
                    let r = self.parse_import_args();
                    self.ctx.no_in = saved_no_in;
                    r
                } else if self.tok.is_kw("defer") {
                    Err(Fail::unsupported("import.defer (deferred imports)"))
                } else {
                    Err(Fail::early("expected 'meta' after 'import.'"))
                }
            }
            _ => Err(Fail::early(
                "import declarations are only valid in modules",
            )),
        }
    }

    fn parse_import_args(&mut self) -> PResult<Expr> {
        let mut args = vec![self.parse_assignment(false)?];
        if self.eat_punct(P::Comma)? && !self.tok.is_punct(P::RParen) {
            args.push(self.parse_assignment(false)?);
            let _ = self.eat_punct(P::Comma)?;
        }
        self.expect_punct(P::RParen, "')' after import()")?;
        Ok(Expr::ImportCall(args))
    }

    /// Parenthesized expression in a non-arrow position.
    fn parse_paren_primary(&mut self) -> PResult<Expr> {
        self.next()?; // (
        let saved_no_in = self.ctx.no_in;
        self.ctx.no_in = false;
        let r = (|| {
            if self.tok.is_punct(P::RParen) || self.tok.is_punct(P::Ellipsis) {
                return Err(Fail::early("unexpected token in parenthesized expression"));
            }
            let e = self.parse_expression()?;
            self.expect_punct(P::RParen, "')'")?;
            Ok(e)
        })();
        self.ctx.no_in = saved_no_in;
        let e = r?;
        if self.tok.is_punct(P::Arrow) && !self.tok.newline_before {
            return Err(Fail::early("arrow function not allowed in this position"));
        }
        Ok(Expr::Paren(Box::new(e)))
    }

    fn parse_array_literal(&mut self) -> PResult<Expr> {
        let saved_no_in = self.ctx.no_in;
        self.ctx.no_in = false;
        let r = self.parse_array_literal_inner();
        self.ctx.no_in = saved_no_in;
        r
    }

    fn parse_array_literal_inner(&mut self) -> PResult<Expr> {
        self.next()?; // [
        let mut elems: Vec<Option<Arg>> = Vec::new();
        let mut trailing_comma = false;
        loop {
            if self.tok.is_punct(P::RBracket) {
                break;
            }
            if self.eat_punct(P::Comma)? {
                elems.push(None);
                continue;
            }
            let item = if self.eat_punct(P::Ellipsis)? {
                Arg::Spread(self.parse_assignment(true)?)
            } else {
                Arg::Expr(self.parse_assignment(true)?)
            };
            elems.push(Some(item));
            if self.tok.is_punct(P::RBracket) {
                trailing_comma = false;
                break;
            }
            self.expect_punct(P::Comma, "',' in array literal")?;
            if self.tok.is_punct(P::RBracket) {
                trailing_comma = true;
                break;
            }
        }
        self.expect_punct(P::RBracket, "']'")?;
        Ok(Expr::Array {
            elems,
            trailing_comma,
        })
    }

    fn parse_object_literal(&mut self) -> PResult<Expr> {
        let saved_no_in = self.ctx.no_in;
        self.ctx.no_in = false;
        let r = self.parse_object_literal_inner();
        self.ctx.no_in = saved_no_in;
        r
    }

    fn parse_object_literal_inner(&mut self) -> PResult<Expr> {
        self.next()?; // {
        let mut props = Vec::new();
        let mut proto_count = 0u32;
        loop {
            if self.tok.is_punct(P::RBrace) {
                break;
            }
            let prop = self.parse_object_prop(&mut proto_count)?;
            props.push(prop);
            if self.tok.is_punct(P::RBrace) {
                break;
            }
            self.expect_punct(P::Comma, "',' in object literal")?;
        }
        self.expect_punct(P::RBrace, "'}'")?;
        Ok(Expr::Object(props))
    }

    fn parse_object_prop(&mut self, proto_count: &mut u32) -> PResult<ObjProp> {
        if self.eat_punct(P::Ellipsis)? {
            return Ok(ObjProp::Spread(self.parse_assignment(true)?));
        }
        // Modifiers.
        let mut is_async = false;
        let mut is_gen = false;
        let mut accessor: Option<MethodKind> = None;
        if self.tok.is_kw("async") {
            let p = self.peek()?;
            if !p.newline_before
                && (self.token_is_property_name_start(&p) || p.is_punct(P::Star))
            {
                is_async = true;
                self.next()?;
            }
        }
        if self.tok.is_punct(P::Star) {
            is_gen = true;
            self.next()?;
        }
        if !is_async && !is_gen && (self.tok.is_kw("get") || self.tok.is_kw("set")) {
            let which = if self.tok.is_kw("get") {
                MethodKind::Get
            } else {
                MethodKind::Set
            };
            let p = self.peek()?;
            if self.token_is_property_name_start(&p) {
                accessor = Some(which);
                self.next()?;
            }
        }
        let key_was_plain_ident =
            matches!(self.tok.kind, TokenKind::Ident(_)) && !self.tok.had_escape;
        let _ = key_was_plain_ident;
        let key_tok_pos = self.tok.start;
        let key_is_ident_tok = matches!(self.tok.kind, TokenKind::Ident(_));
        let key = self.parse_property_name()?;
        if matches!(key, PropKey::Private(_)) {
            return Err(Fail::early("private name in object literal"));
        }
        // Method.
        if self.tok.is_punct(P::LParen) {
            let kind = accessor.clone().unwrap_or(MethodKind::Method);
            let func = self.parse_method_function(is_async, is_gen, &kind, false)?;
            return Ok(ObjProp::Method { kind, key, func });
        }
        if is_async || is_gen || accessor.is_some() {
            return Err(Fail::early("expected '(' after method name"));
        }
        // key : value
        if self.eat_punct(P::Colon)? {
            if self.non_computed_key_string(&key).as_deref() == Some("__proto__") {
                *proto_count += 1;
                if *proto_count > 1 && self.pending.dup_proto.is_none() {
                    self.pending.dup_proto = Some(key_tok_pos);
                }
            }
            let value = self.parse_assignment(true)?;
            return Ok(ObjProp::KeyValue { key, value });
        }
        // Shorthand / CoverInitializedName.
        if key_is_ident_tok {
            let name = match &key {
                PropKey::Ident(n) => n.clone(),
                _ => unreachable!(),
            };
            self.check_ident_ref(&name)?;
            if self.eat_punct(P::Eq)? {
                if self.pending.cover_init.is_none() {
                    self.pending.cover_init = Some(key_tok_pos);
                }
                let value = self.parse_assignment(false)?;
                return Ok(ObjProp::CoverInit(name, Box::new(value)));
            }
            return Ok(ObjProp::Shorthand(name));
        }
        Err(Fail::early("expected ':' after property key"))
    }

    pub fn parse_property_name(&mut self) -> PResult<PropKey> {
        match &self.tok.kind {
            TokenKind::Ident(n) => {
                let n = n.clone();
                self.next()?;
                Ok(PropKey::Ident(n))
            }
            TokenKind::Str { raw, flags } => {
                if self.ctx.strict && flags.legacy_octal_escape {
                    return Err(Fail::early("octal escape sequence in strict mode"));
                }
                if self.ctx.strict && flags.non_octal_escape {
                    return Err(Fail::early("\\8 and \\9 escapes in strict mode"));
                }
                let Some(cooked) = cook_string(raw, *flags) else {
                    return Err(Fail::unsupported(
                        "lone surrogate in string property key",
                    ));
                };
                self.next()?;
                Ok(PropKey::Str(cooked))
            }
            TokenKind::Num { raw, flags } => {
                if self.ctx.strict && flags.legacy_octal {
                    return Err(Fail::early("legacy octal literal in strict mode"));
                }
                if self.ctx.strict && flags.non_octal_decimal {
                    return Err(Fail::early(
                        "decimal literal with leading zero in strict mode",
                    ));
                }
                let raw = raw.clone();
                self.next()?;
                Ok(PropKey::Num(raw))
            }
            TokenKind::PrivateIdent(n) => {
                let n = n.clone();
                self.next()?;
                Ok(PropKey::Private(n))
            }
            TokenKind::Punct(P::LBracket) => {
                self.next()?;
                let saved_no_in = self.ctx.no_in;
                self.ctx.no_in = false;
                let e = self.parse_assignment(false);
                self.ctx.no_in = saved_no_in;
                let e = e?;
                self.expect_punct(P::RBracket, "']' after computed key")?;
                Ok(PropKey::Computed(Box::new(e)))
            }
            _ => Err(Fail::early("expected property name")),
        }
    }

    // ---- templates ------------------------------------------------------

    fn parse_tagged_template(&mut self, tag: Expr) -> PResult<Expr> {
        let (quasis, exprs) = self.parse_template_parts(true)?;
        Ok(Expr::TaggedTemplate {
            tag: Box::new(tag),
            quasis,
            exprs,
        })
    }

    fn parse_template_parts(&mut self, tagged: bool) -> PResult<(Vec<String>, Vec<Expr>)> {
        let mut quasis = Vec::new();
        let mut exprs = Vec::new();
        // Current token is NoSub or Head.
        let (kind, raw) = self.template_piece(tagged)?;
        quasis.push(raw);
        if kind == TplKind::NoSub {
            self.next()?;
            return Ok((quasis, exprs));
        }
        self.next()?;
        loop {
            let saved_no_in = self.ctx.no_in;
            self.ctx.no_in = false;
            let e = self.parse_expression();
            self.ctx.no_in = saved_no_in;
            exprs.push(e?);
            if !self.tok.is_punct(P::RBrace) {
                return Err(Fail::early("expected '}' in template substitution"));
            }
            self.tok = self.lx.relex_template_continue(self.tok.start)?;
            let (kind, raw) = self.template_piece(tagged)?;
            quasis.push(raw);
            self.next()?;
            if kind == TplKind::Tail {
                break;
            }
        }
        Ok((quasis, exprs))
    }

    fn template_piece(&self, tagged: bool) -> PResult<(TplKind, String)> {
        match &self.tok.kind {
            TokenKind::Template {
                kind,
                raw,
                invalid_escape,
                octal_escape,
            } => {
                if !tagged && (*invalid_escape || *octal_escape) {
                    return Err(Fail::early("invalid escape in template literal"));
                }
                Ok((*kind, raw.clone()))
            }
            _ => Err(Fail::early("expected template piece")),
        }
    }
}
