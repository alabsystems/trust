//! A focused recursive-descent parser from **real TypeScript source text** to
//! `TsCore`. This is the front edge of autoformalization: the system now ingests
//! actual `.ts` (not a hand-built AST). It covers the deterministic integer-reducer
//! fragment — `function`s over `number`/`number[]`/record params with `const`/`let`/
//! `return`/bounded-`for`, arithmetic and comparison operators, `&&`/`||`, the
//! ternary `?:`, `Math.min`/`Math.max`, array indexing `a[e]`, and field access
//! `o.f`. Anything outside fails CLOSED with a precise `ParseError` (never a silent
//! partial program), exactly like the deriver's `FragmentEscape`.
//!
//! `number` is modeled as an unsigned integer of width `NUM_W` here (the
//! deterministic-int gate); a producer that knows a tighter width can post-narrow
//! the `TsCore`.

use crate::core::{TsExpr, TsFunction, TsStmt, TsTy, TsVar};
use trust_types::BinOp;

/// Width `number` is modeled at (the deterministic integer gate). 16 bits keeps the
/// SMT domain small (terminal coordinates fit); the structural refinement proofs are
/// width-independent, so this is a modeling choice, not a soundness one.
const NUM_W: u32 = 16;

/// A fail-closed parse error: the source is outside the admitted fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError(pub String);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypeScript parse/fragment error: {}", self.0)
    }
}
impl std::error::Error for ParseError {}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Num(i128),
    Ident(String),
    Punct(&'static str),
}

fn lex(src: &str) -> Result<Vec<Tok>, ParseError> {
    let b = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    // Multi-char operators first; order matters (longest match).
    const OPS: &[&str] = &[
        "===", "!==", "&&", "||", "<=", ">=", "++", "=>", "(", ")", "{", "}", "[", "]", ",", ";",
        ":", "?", ".", "=", "<", ">", "+", "-", "*", "/", "%",
    ];
    while i < b.len() {
        let c = b[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if c == b'/' && i + 1 < b.len() && b[i + 1] == b'/' {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if c.is_ascii_digit() {
            let start = i;
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
            let n: i128 = src[start..i].parse().map_err(|_| ParseError("bad number".into()))?;
            out.push(Tok::Num(n));
            continue;
        }
        if c == b'_' || c.is_ascii_alphabetic() {
            let start = i;
            while i < b.len() && (b[i] == b'_' || b[i].is_ascii_alphanumeric()) {
                i += 1;
            }
            out.push(Tok::Ident(src[start..i].to_string()));
            continue;
        }
        let rest = &src[i..];
        let op = OPS.iter().find(|o| rest.starts_with(**o));
        match op {
            Some(o) => {
                out.push(Tok::Punct(o));
                i += o.len();
            }
            None => return Err(ParseError(format!("unexpected character `{}`", c as char))),
        }
    }
    Ok(out)
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
    /// Module-level `enum`s: name → (member → integer value). `EnumName.Member`
    /// resolves to its constant; an enum-typed parameter is an integer.
    enums: std::collections::HashMap<String, std::collections::HashMap<String, i128>>,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }
    fn next(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn eat_punct(&mut self, p: &str) -> Result<(), ParseError> {
        match self.next() {
            Some(Tok::Punct(q)) if q == p => Ok(()),
            other => Err(ParseError(format!("expected `{p}`, found {other:?}"))),
        }
    }
    fn is_punct(&self, p: &str) -> bool {
        matches!(self.peek(), Some(Tok::Punct(q)) if *q == p)
    }
    fn eat_ident(&mut self) -> Result<String, ParseError> {
        match self.next() {
            Some(Tok::Ident(s)) => Ok(s),
            other => Err(ParseError(format!("expected identifier, found {other:?}"))),
        }
    }
    fn eat_kw(&mut self, kw: &str) -> Result<(), ParseError> {
        match self.next() {
            Some(Tok::Ident(s)) if s == kw => Ok(()),
            other => Err(ParseError(format!("expected `{kw}`, found {other:?}"))),
        }
    }
}

/// Parse a single TypeScript `function` declaration into a [`TsFunction`].
pub fn parse_function(src: &str) -> Result<TsFunction, ParseError> {
    let mut p = Parser { toks: lex(src)?, pos: 0, enums: std::collections::HashMap::new() };
    parse_function_from(&mut p)
}

/// Parse one `function` declaration from an in-progress token stream.
fn parse_function_from(p: &mut Parser) -> Result<TsFunction, ParseError> {
    // A pure `async function` (no real effect) is its synchronous body; `await` of
    // an external/unknown call still fails closed at inlining, so this is sound.
    if matches!(p.peek(), Some(Tok::Ident(k)) if k == "async") {
        p.next();
    }
    p.eat_kw("function")?;
    let name = p.eat_ident()?;
    p.eat_punct("(")?;
    let mut params = Vec::new();
    while !p.is_punct(")") {
        let pname = p.eat_ident()?;
        p.eat_punct(":")?;
        let ty = parse_ty(p)?;
        params.push(TsVar::new(pname, ty));
        if p.is_punct(",") {
            p.eat_punct(",")?;
        }
    }
    p.eat_punct(")")?;
    p.eat_punct(":")?;
    let ret = parse_ty(p)?;
    p.eat_punct("{")?;
    let body = parse_block(p)?;
    p.eat_punct("}")?;
    Ok(TsFunction { def_path: name.clone(), name, params, body, ret })
}

/// A type annotation: `number`, `boolean`, `number[]`, or a `{f: number, ...}`
/// record (the record shape is informational — fields are referenced via `o.f`).
fn parse_ty(p: &mut Parser) -> Result<TsTy, ParseError> {
    // Arrow function type `(params) => T` — a function-reference parameter (a
    // callback). Modeled as a skip-from-scalar-env placeholder; it is only ever a
    // call target, specialized away by inlining when bound to a named function.
    if p.is_punct("(") {
        p.eat_punct("(")?;
        let mut depth = 1;
        while depth > 0 {
            match p.next() {
                Some(Tok::Punct("(")) => depth += 1,
                Some(Tok::Punct(")")) => depth -= 1,
                Some(_) => {}
                None => return Err(ParseError("unterminated function type".into())),
            }
        }
        p.eat_punct("=>")?;
        let _ = parse_ty(p)?;
        return Ok(TsTy::array(NUM_W, 0));
    }
    if p.is_punct("{") {
        // record: skip to the matching `}` (fields are accessed positionally by name)
        p.eat_punct("{")?;
        let mut depth = 1;
        while depth > 0 {
            match p.next() {
                Some(Tok::Punct("{")) => depth += 1,
                Some(Tok::Punct("}")) => depth -= 1,
                Some(_) => {}
                None => return Err(ParseError("unterminated record type".into())),
            }
        }
        // Modeled as a 0-length array placeholder; field access uses `o.f` vars.
        return Ok(TsTy::Arr { elem_width: NUM_W, len: 0 });
    }
    let name = p.eat_ident()?;
    // `Promise<T>` — a pure async return type resolves to its inner `T`.
    if name == "Promise" {
        p.eat_punct("<")?;
        let inner = parse_ty(p)?;
        p.eat_punct(">")?;
        return Ok(inner);
    }
    // An enum-typed parameter is an integer (its members are integer constants).
    if p.enums.contains_key(&name) {
        return Ok(TsTy::uint(NUM_W));
    }
    let base = match name.as_str() {
        "number" => TsTy::uint(NUM_W),
        "boolean" => TsTy::Bool,
        // A `string` is modeled as a fixed-length array of UTF-16 char codes;
        // `s.charCodeAt(i)` reads an element, `s.length` is a symbolic field.
        "string" => return Ok(TsTy::array(NUM_W, 8)),
        other => return Err(ParseError(format!("unsupported type `{other}`"))),
    };
    if p.is_punct("[") {
        p.eat_punct("[")?;
        p.eat_punct("]")?;
        // Length is fixed by the producer/loop bound; default a small demo length.
        return Ok(TsTy::array(NUM_W, 8));
    }
    Ok(base)
}

fn parse_block(p: &mut Parser) -> Result<Vec<TsStmt>, ParseError> {
    let mut stmts = Vec::new();
    while !p.is_punct("}") {
        stmts.push(parse_stmt(p)?);
    }
    Ok(stmts)
}

fn parse_stmt(p: &mut Parser) -> Result<TsStmt, ParseError> {
    match p.peek() {
        Some(Tok::Ident(k)) if k == "const" || k == "let" => {
            p.next();
            let name = p.eat_ident()?;
            // optional `: type`
            let mut ty = TsTy::uint(NUM_W);
            if p.is_punct(":") {
                p.eat_punct(":")?;
                ty = parse_ty(p)?;
            }
            p.eat_punct("=")?;
            let value = parse_expr(p)?;
            p.eat_punct(";")?;
            Ok(TsStmt::Assign { var: TsVar::new(name, ty), value })
        }
        Some(Tok::Ident(k)) if k == "return" => {
            p.next();
            let value = parse_expr(p)?;
            p.eat_punct(";")?;
            Ok(TsStmt::Return { value })
        }
        Some(Tok::Ident(k)) if k == "for" => parse_for(p),
        Some(Tok::Ident(k)) if k == "switch" => parse_switch(p),
        // bare assignment `x = e;`
        Some(Tok::Ident(_)) => {
            let name = p.eat_ident()?;
            p.eat_punct("=")?;
            let value = parse_expr(p)?;
            p.eat_punct(";")?;
            Ok(TsStmt::Assign { var: TsVar::new(name, TsTy::uint(NUM_W)), value })
        }
        other => Err(ParseError(format!("unexpected statement start {other:?}"))),
    }
}

/// `for (let i = 0; i < COUNT; i++) { body }` — a statically-bounded loop.
fn parse_for(p: &mut Parser) -> Result<TsStmt, ParseError> {
    p.eat_kw("for")?;
    p.eat_punct("(")?;
    p.eat_kw("let")?;
    let var = p.eat_ident()?;
    p.eat_punct("=")?;
    match p.next() {
        Some(Tok::Num(0)) => {}
        other => return Err(ParseError(format!("loop must start at 0, found {other:?}"))),
    }
    p.eat_punct(";")?;
    let cond_var = p.eat_ident()?;
    p.eat_punct("<")?;
    let count = match p.next() {
        Some(Tok::Num(n)) if n >= 0 => n as u32,
        other => return Err(ParseError(format!("loop bound must be a constant, found {other:?}"))),
    };
    if cond_var != var {
        return Err(ParseError("loop condition var must match the counter".into()));
    }
    p.eat_punct(";")?;
    let inc_var = p.eat_ident()?;
    p.eat_punct("++")?;
    if inc_var != var {
        return Err(ParseError("loop increment var must match the counter".into()));
    }
    p.eat_punct(")")?;
    p.eat_punct("{")?;
    let body = parse_block(p)?;
    p.eat_punct("}")?;
    Ok(TsStmt::ForRange { var, count, body })
}

/// `switch (e) { case C: return E; ... default: return D; }` — desugars to a nested
/// `If`-return `return (e === C ? E : ... : D)`. Each case must `return` (no
/// fall-through); a `default` is required. This is the idiomatic state-machine
/// dispatch the VT parser uses.
fn parse_switch(p: &mut Parser) -> Result<TsStmt, ParseError> {
    p.eat_kw("switch")?;
    p.eat_punct("(")?;
    let discr = parse_expr(p)?;
    p.eat_punct(")")?;
    p.eat_punct("{")?;
    let mut cases: Vec<(TsExpr, TsExpr)> = Vec::new();
    let mut default: Option<TsExpr> = None;
    let arm = |p: &mut Parser| -> Result<TsExpr, ParseError> {
        p.eat_punct(":")?;
        p.eat_kw("return")?;
        let e = parse_expr(p)?;
        p.eat_punct(";")?;
        Ok(e)
    };
    while !p.is_punct("}") {
        match p.peek() {
            Some(Tok::Ident(k)) if k == "case" => {
                p.next();
                let cval = parse_expr(p)?;
                cases.push((cval, arm(p)?));
            }
            Some(Tok::Ident(k)) if k == "default" => {
                p.next();
                default = Some(arm(p)?);
            }
            other => return Err(ParseError(format!("switch: expected case/default, found {other:?}"))),
        }
    }
    p.eat_punct("}")?;
    let mut acc = default.ok_or_else(|| ParseError("switch must have a default".into()))?;
    for (cval, rexpr) in cases.into_iter().rev() {
        let cond = TsExpr::Bin {
            op: BinOp::Eq,
            lhs: Box::new(discr.clone()),
            rhs: Box::new(cval),
            ty: TsTy::Bool,
        };
        acc = TsExpr::If {
            cond: Box::new(cond),
            then_e: Box::new(rexpr),
            else_e: Box::new(acc),
            ty: TsTy::uint(NUM_W),
        };
    }
    Ok(TsStmt::Return { value: acc })
}

// --- Pratt expression parser ------------------------------------------------

fn parse_expr(p: &mut Parser) -> Result<TsExpr, ParseError> {
    parse_ternary(p)
}

fn parse_ternary(p: &mut Parser) -> Result<TsExpr, ParseError> {
    let cond = parse_binary(p, 0)?;
    if p.is_punct("?") {
        p.eat_punct("?")?;
        let then_e = parse_expr(p)?;
        p.eat_punct(":")?;
        let else_e = parse_expr(p)?;
        let ty = then_e.ty();
        return Ok(TsExpr::If {
            cond: Box::new(cond),
            then_e: Box::new(then_e),
            else_e: Box::new(else_e),
            ty,
        });
    }
    Ok(cond)
}

/// Binary operators by precedence (lowest binds first): `||` < `&&` < comparisons
/// < additive < multiplicative.
fn parse_binary(p: &mut Parser, min_prec: u8) -> Result<TsExpr, ParseError> {
    let mut lhs = parse_unary(p)?;
    loop {
        let (op, prec, is_bool) = match p.peek() {
            Some(Tok::Punct("||")) => (BinOp::BitOr, 1, true),
            Some(Tok::Punct("&&")) => (BinOp::BitAnd, 2, true),
            Some(Tok::Punct("===")) => (BinOp::Eq, 3, true),
            Some(Tok::Punct("!==")) => (BinOp::Ne, 3, true),
            Some(Tok::Punct("<")) => (BinOp::Lt, 3, true),
            Some(Tok::Punct("<=")) => (BinOp::Le, 3, true),
            Some(Tok::Punct(">")) => (BinOp::Gt, 3, true),
            Some(Tok::Punct(">=")) => (BinOp::Ge, 3, true),
            Some(Tok::Punct("+")) => (BinOp::Add, 4, false),
            Some(Tok::Punct("-")) => (BinOp::Sub, 4, false),
            Some(Tok::Punct("*")) => (BinOp::Mul, 5, false),
            Some(Tok::Punct("/")) => (BinOp::Div, 5, false),
            Some(Tok::Punct("%")) => (BinOp::Rem, 5, false),
            _ => break,
        };
        if prec < min_prec {
            break;
        }
        p.next();
        let rhs = parse_binary(p, prec + 1)?;
        let ty = if is_bool { TsTy::Bool } else { lhs.ty() };
        lhs = TsExpr::Bin { op, lhs: Box::new(lhs), rhs: Box::new(rhs), ty };
    }
    Ok(lhs)
}

fn parse_unary(p: &mut Parser) -> Result<TsExpr, ParseError> {
    // `await EXPR` — for a pure async value, await is the identity (it unwraps the
    // resolved value). An `await` of an external/unknown call fails closed later at
    // inlining, so effectful async never silently passes.
    if matches!(p.peek(), Some(Tok::Ident(k)) if k == "await") {
        p.next();
        return parse_unary(p);
    }
    parse_postfix(p)
}

fn parse_postfix(p: &mut Parser) -> Result<TsExpr, ParseError> {
    let mut e = parse_primary(p)?;
    loop {
        if p.is_punct(".") {
            // field access (or a `s.charCodeAt(i)` string read) on an identifier base
            let TsExpr::Var(v) = &e else {
                return Err(ParseError("field access requires a variable base".into()));
            };
            let base = v.name.clone();
            p.eat_punct(".")?;
            let field = p.eat_ident()?;
            // `EnumName.Member` resolves to its integer constant.
            if let Some(val) = p.enums.get(&base).and_then(|m| m.get(&field)) {
                e = TsExpr::Int(*val, TsTy::uint(NUM_W));
            } else if field == "charCodeAt" {
                p.eat_punct("(")?;
                let idx = parse_expr(p)?;
                p.eat_punct(")")?;
                e = match idx {
                    TsExpr::Int(k, _) if k >= 0 => TsExpr::index(base, NUM_W, k as u32),
                    TsExpr::Var(iv) => TsExpr::index_var(base, NUM_W, iv.name),
                    other => TsExpr::index_expr(base, NUM_W, other),
                };
            } else if p.is_punct("(") {
                // Method call `obj.method(args)` -> Call(method, [this=obj, args...]).
                p.eat_punct("(")?;
                let mut args = vec![TsExpr::Var(TsVar::new(base, TsTy::array(NUM_W, 0)))];
                while !p.is_punct(")") {
                    args.push(parse_expr(p)?);
                    if p.is_punct(",") {
                        p.eat_punct(",")?;
                    }
                }
                p.eat_punct(")")?;
                e = TsExpr::Call { func: field, args };
            } else {
                e = TsExpr::field(base, field, NUM_W);
            }
        } else if p.is_punct("[") {
            let TsExpr::Var(v) = &e else {
                return Err(ParseError("indexing requires a variable base".into()));
            };
            let base = v.name.clone();
            p.eat_punct("[")?;
            let idx = parse_expr(p)?;
            p.eat_punct("]")?;
            e = match idx {
                TsExpr::Int(k, _) if k >= 0 => TsExpr::index(base, NUM_W, k as u32),
                TsExpr::Var(iv) => TsExpr::index_var(base, NUM_W, iv.name),
                other => TsExpr::index_expr(base, NUM_W, other),
            };
        } else {
            break;
        }
    }
    Ok(e)
}

fn parse_primary(p: &mut Parser) -> Result<TsExpr, ParseError> {
    match p.next() {
        Some(Tok::Num(n)) => Ok(TsExpr::Int(n, TsTy::uint(NUM_W))),
        Some(Tok::Punct("(")) => {
            let e = parse_expr(p)?;
            p.eat_punct(")")?;
            Ok(e)
        }
        Some(Tok::Punct("-")) => {
            // unary minus on a literal (signed constant)
            match p.next() {
                Some(Tok::Num(n)) => Ok(TsExpr::Int(-n, TsTy::sint(NUM_W))),
                other => Err(ParseError(format!("expected number after unary `-`, found {other:?}"))),
            }
        }
        Some(Tok::Ident(id)) => {
            match id.as_str() {
                "true" => Ok(TsExpr::Bool(true)),
                "false" => Ok(TsExpr::Bool(false)),
                "Math" => {
                    p.eat_punct(".")?;
                    let m = p.eat_ident()?;
                    p.eat_punct("(")?;
                    let a = parse_expr(p)?;
                    p.eat_punct(",")?;
                    let b = parse_expr(p)?;
                    p.eat_punct(")")?;
                    let ty = a.ty();
                    match m.as_str() {
                        "min" => Ok(TsExpr::min(a, b, ty)),
                        "max" => Ok(TsExpr::max(a, b, ty)),
                        other => Err(ParseError(format!("unsupported Math.{other}"))),
                    }
                }
                // `f(args)` — a call to a sibling function (resolved by inlining).
                _ if p.is_punct("(") => {
                    p.eat_punct("(")?;
                    let mut args = Vec::new();
                    while !p.is_punct(")") {
                        args.push(parse_expr(p)?);
                        if p.is_punct(",") {
                            p.eat_punct(",")?;
                        }
                    }
                    p.eat_punct(")")?;
                    Ok(TsExpr::Call { func: id, args })
                }
                _ => Ok(TsExpr::Var(TsVar::new(id, TsTy::uint(NUM_W)))),
            }
        }
        other => Err(ParseError(format!("unexpected token in expression: {other:?}"))),
    }
}

/// Parse a MODULE: `function` declarations and/or `class` declarations (whose
/// methods desugar to functions over the instance record), so calls between them
/// resolve by inlining. Fails closed on any other top-level construct.
pub fn parse_module(src: &str) -> Result<Vec<TsFunction>, ParseError> {
    let mut p = Parser { toks: lex(src)?, pos: 0, enums: std::collections::HashMap::new() };
    let mut funcs = Vec::new();
    while p.peek().is_some() {
        match p.peek() {
            Some(Tok::Ident(k)) if k == "enum" => parse_enum_into(&mut p)?,
            Some(Tok::Ident(k)) if k == "class" => funcs.extend(parse_class_from(&mut p)?),
            _ => funcs.push(parse_function_from(&mut p)?),
        }
    }
    if funcs.is_empty() {
        return Err(ParseError("module has no declarations".into()));
    }
    Ok(funcs)
}

/// Parse `enum Name { A, B = 5, C }` into the parser's enum table (member values
/// auto-increment from 0, or from an explicit `= N`). `Name.Member` then resolves
/// to its integer constant during expression parsing.
fn parse_enum_into(p: &mut Parser) -> Result<(), ParseError> {
    p.eat_kw("enum")?;
    let name = p.eat_ident()?;
    p.eat_punct("{")?;
    let mut members = std::collections::HashMap::new();
    let mut next_val = 0i128;
    while !p.is_punct("}") {
        let m = p.eat_ident()?;
        let val = if p.is_punct("=") {
            p.eat_punct("=")?;
            match p.next() {
                Some(Tok::Num(n)) => n,
                other => return Err(ParseError(format!("enum value must be a literal, found {other:?}"))),
            }
        } else {
            next_val
        };
        members.insert(m, val);
        next_val = val + 1;
        if p.is_punct(",") {
            p.eat_punct(",")?;
        }
    }
    p.eat_punct("}")?;
    p.enums.insert(name, members);
    Ok(())
}

/// Desugar a `class` into its methods as functions. A pure (immutable) method
/// `m(args): T { ... this.f ... }` becomes `m(this: record, args): T { ... }`;
/// field declarations are informational; a `constructor` body is skipped (instances
/// are modeled structurally by their fields).
fn parse_class_from(p: &mut Parser) -> Result<Vec<TsFunction>, ParseError> {
    p.eat_kw("class")?;
    let cname = p.eat_ident()?;
    p.eat_punct("{")?;
    let mut methods = Vec::new();
    while !p.is_punct("}") {
        let member = p.eat_ident()?;
        // Field declaration: `name : type ;`
        if p.is_punct(":") {
            p.eat_punct(":")?;
            let _ = parse_ty(p)?;
            if p.is_punct(";") {
                p.eat_punct(";")?;
            }
            continue;
        }
        // Method / constructor: `( params ) ...`
        p.eat_punct("(")?;
        let mut params = vec![TsVar::new("this", TsTy::array(NUM_W, 0))];
        while !p.is_punct(")") {
            let pn = p.eat_ident()?;
            p.eat_punct(":")?;
            let ty = parse_ty(p)?;
            params.push(TsVar::new(pn, ty));
            if p.is_punct(",") {
                p.eat_punct(",")?;
            }
        }
        p.eat_punct(")")?;
        if member == "constructor" {
            // Skip the constructor body — instances are structural.
            p.eat_punct("{")?;
            let mut depth = 1;
            while depth > 0 {
                match p.next() {
                    Some(Tok::Punct("{")) => depth += 1,
                    Some(Tok::Punct("}")) => depth -= 1,
                    Some(_) => {}
                    None => return Err(ParseError("unterminated constructor".into())),
                }
            }
            continue;
        }
        p.eat_punct(":")?;
        let ret = parse_ty(p)?;
        p.eat_punct("{")?;
        let body = parse_block(p)?;
        p.eat_punct("}")?;
        methods.push(TsFunction {
            name: member.clone(),
            def_path: format!("{cname}.{member}"),
            params,
            body,
            ret,
        });
    }
    p.eat_punct("}")?;
    if methods.is_empty() {
        return Err(ParseError(format!("class `{cname}` has no methods")));
    }
    Ok(methods)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_a_real_arithmetic_reducer() {
        let src = r#"
            function cursorForward(col: number, n: number): number {
                const sum = col + n;
                return Math.min(sum, 7);
            }
        "#;
        let f = parse_function(src).expect("parses");
        assert_eq!(f.name, "cursorForward");
        assert_eq!(f.params.len(), 2);
        assert_eq!(f.body.len(), 2);
    }

    #[test]
    fn parses_ternary_and_comparison() {
        let src = r#"
            function clamp(x: number, lo: number, hi: number): number {
                return x < lo ? lo : (x > hi ? hi : x);
            }
        "#;
        let f = parse_function(src).expect("parses");
        assert!(matches!(f.body[0], TsStmt::Return { .. }));
    }

    #[test]
    fn parses_a_bounded_loop_over_an_array() {
        let src = r#"
            function arrayMax(a: number[]): number {
                let acc = 0;
                for (let i = 0; i < 4; i++) {
                    acc = Math.max(acc, a[i]);
                }
                return acc;
            }
        "#;
        let f = parse_function(src).expect("parses");
        assert!(matches!(f.body[1], TsStmt::ForRange { count: 4, .. }));
    }

    #[test]
    fn parses_a_string_reducer() {
        let src = "function sumFirst4(s: string): number { \
                       let acc = 0; \
                       for (let i = 0; i < 4; i++) { acc = acc + s.charCodeAt(i); } \
                       return acc; }";
        let f = parse_function(src).expect("parses");
        assert_eq!(f.params.len(), 1);
        assert!(matches!(f.body[1], TsStmt::ForRange { count: 4, .. }));
    }

    #[test]
    fn out_of_fragment_syntax_fails_closed() {
        // `async` and arrow functions / unknown statements are rejected.
        assert!(parse_function("function f(): number { while (true) {} }").is_err());
        assert!(parse_function("const x = 3;").is_err()); // not a function decl
        assert!(parse_function("function f(x: any): number { return 0; }").is_err()); // unsupported type
        assert!(parse_function("function* g(): number { return 0; }").is_err()); // generator
        assert!(parse_function("function f(): number { return new Foo(); }").is_err()); // new
        // A PURE async function IS in-fragment (no real effect):
        assert!(parse_function("async function f(c: number): Promise<number> { return c; }").is_ok());
    }
}
