// Recursive-descent parser for the bootstrap slice, written from the ECMA-262
// grammar. Every out-of-slice construct is an Err — the caller maps that to
// NoCoverage, so an incomplete parser can never masquerade as a SyntaxError.
// Early errors we cannot fully check (lexical redeclaration webs) are refused
// conservatively rather than mis-accepted.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::ast::{
    BinOp, BindTarget, ClassKey, ClassLit, ClassMember, DeclKind, Expr, ForInOfLeft, FuncLit,
    LogOp, MemberProp, MethodKind, ObjKey, Param, PatElem, Pattern, Program, PropDef, Stmt,
    TplPart, UnOp,
};
use crate::lexer::{Lexer, Tok, Token, TplPiece};
use crate::value::units_from_str;
use std::collections::HashSet;
use std::rc::Rc;

type R<T> = Result<T, String>;

const MAX_PARSE_DEPTH: u32 = 256;

/// Binary-operator precedence anchors used in two places each (the operator
/// table + the private-in ShiftExpression cut). Higher binds tighter.
const REL_PREC: u8 = 6; // relational: < <= > >= instanceof in
const SHIFT_PREC: u8 = 7; // shift: << >> >>>


/// Internal marker distinguishing a fully-specified early Syntax Error from
/// an out-of-slice refusal while errors bubble as strings. (Shared with the
/// lexer for the string-escape early errors.)
pub(crate) const EARLY_SYNTAX: &str = "\u{1}early-syntax\u{1}";

pub(crate) fn early_syntax(msg: &str) -> String {
    format!("{EARLY_SYNTAX}{msg}")
}

/// Why a parse did not produce a Program.
#[derive(Debug)]
pub enum ParseFail {
    /// The source uses syntax outside the bootstrap slice — the caller must
    /// refuse the case (NoCoverage), never guess a SyntaxError.
    OutOfSlice(String),
    /// A fully-specified EARLY ERROR: a conforming engine throws SyntaxError
    /// while parsing this exact source (strict `eval`/`arguments` bindings
    /// and targets, duplicate `__proto__` data properties, catch-parameter/
    /// lexical redeclaration). This is an exact observable, emitted only
    /// where the spec mandates it with zero engine latitude.
    EarlySyntaxError(String),
}

impl std::fmt::Display for ParseFail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseFail::OutOfSlice(m) => write!(f, "{m}"),
            ParseFail::EarlySyntaxError(m) => write!(f, "early SyntaxError: {m}"),
        }
    }
}

/// Words never usable as plain identifiers/bindings in the slice. `let` is
/// included (its sloppy identifier use is refused, not mis-parsed).
fn is_reserved(id: &str) -> bool {
    matches!(
        id,
        "var" | "let" | "const" | "function" | "return" | "if" | "else" | "while" | "do" | "for"
            | "break" | "continue" | "throw" | "try" | "catch" | "finally" | "switch" | "case"
            | "default" | "new" | "typeof" | "instanceof" | "true" | "false" | "null" | "this"
            | "in" | "delete" | "void" | "class" | "extends" | "super" | "import" | "export"
            | "yield" | "await" | "debugger" | "with" | "enum" | "static" | "implements"
            | "interface" | "package" | "private" | "protected" | "public"
    )
}

/// The spec ReservedWord set (StringValue comparison for ESCAPED
/// identifiers). `await`/`yield` are contextually legal identifiers in
/// (sloppy, non-generator) scripts; strict mode adds the future-reserved set
/// and `let`/`static`/`yield`.
fn is_true_reserved(id: &str, strict: bool) -> bool {
    matches!(
        id,
        "break" | "case" | "catch" | "class" | "const" | "continue" | "debugger" | "default"
            | "delete" | "do" | "else" | "enum" | "export" | "extends" | "false" | "finally"
            | "for" | "function" | "if" | "import" | "in" | "instanceof" | "new" | "null"
            | "return" | "super" | "switch" | "this" | "throw" | "true" | "try" | "typeof"
            | "var" | "void" | "while" | "with"
    ) || (strict
        && matches!(
            id,
            "implements" | "interface" | "let" | "package" | "private" | "protected"
                | "public" | "static" | "yield"
        ))
}

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
    depth: u32,
    strict: bool,
    in_function: bool,
    breakable: u32,
    continuable: u32,
    /// The [~In] grammar parameter: inside a for-statement head, a top-level
    /// `in` terminates the expression instead of parsing as the operator.
    no_in: bool,
    /// The current function body mentioned `arguments` (drives arguments-
    /// object creation at call time). Saved/restored around nested functions.
    uses_arguments: bool,
    /// Inside a MethodDefinition (class method/accessor/ctor/field init):
    /// `super.x` references are legal.
    in_method: bool,
    /// Inside a derived-class constructor: `super(...)` is legal.
    in_derived_ctor: bool,
    /// Inside a class field initializer: `arguments` is a pinned SyntaxError.
    forbid_arguments: bool,
    /// Inside a generator body: `yield`/`yield*` are YieldExpressions and
    /// `yield` may not be used as an identifier (a Syntax Error). Saved and
    /// restored around every nested function/arrow.
    in_generator: bool,
    /// Inside an async function/arrow/method BODY: `await UnaryExpression` is an
    /// AwaitExpression. Saved and restored around every nested function/arrow
    /// (the formal parameters are parsed with `in_async` false, so an `await`
    /// there falls to the out-of-slice path rather than mis-parsing).
    in_async: bool,
    /// Cover-grammar bookkeeping: `{ a = 1 }` CoverInitializedName entries are
    /// only legal when the literal reparses as an assignment pattern; any
    /// surviving at end of parse is a pinned SyntaxError.
    cover_init_count: u32,
    /// OBJECT spread (`{ ...x }`) count: object spread is legal only when the
    /// literal reparses as a pattern (object rest); a surviving object spread
    /// (unmodeled — it copies own enumerable properties) refuses at end of
    /// parse. Array-literal spread (`[...x]`) is fully supported and does NOT
    /// count here.
    obj_spread_count: u32,
    /// `__proto__ : v` colon-form accounting, judged at end of parse for
    /// literals that did NOT reparse as patterns: one duplicate-carrying
    /// literal = pinned SyntaxError; a single one sets [[Prototype]] —
    /// unmodeled, refuses.
    proto_single_count: u32,
    proto_dup_count: u32,
    /// A `{...}` with duplicate `__proto__` data properties was parsed. The
    /// B.3.1 early error is judged only at END of program parse: if the
    /// brace form was actually a destructuring pattern (where duplicates are
    /// LEGAL), the reparse-as-pattern position has already aborted the parse
    /// as out-of-slice, so the flag can only fire for genuine ObjectLiterals.
    saw_proto_dup: bool,
    /// The stack of enclosing class PrivateEnvironments being parsed (9.2):
    /// declared private names (for duplicate + AllPrivateIdentifiersValid
    /// early errors) and deferred references (forward references are legal, so
    /// resolution happens at class-body close).
    priv_stack: Vec<PrivScope>,
    /// Private references seen with no enclosing class in THIS (sub-)parser:
    /// a template-substitution sub-parser bubbles them to its parent; the
    /// top-level parser never fills this (a private ref with no class errors).
    pending_priv_refs: Vec<String>,
    /// True in a template-substitution sub-parser (its `pending_priv_refs`
    /// bubble to the parent instead of erroring).
    is_sub: bool,
}

/// The kind of a private class element (for the duplicate-name early error).
#[derive(Clone, Copy, PartialEq, Eq)]
enum PrivDeclKind {
    Field,
    Method,
    Get,
    Set,
}

/// One class's PrivateEnvironment, filled as its body is parsed.
struct PrivScope {
    /// Declared name → the (kind, is_static) entries seen for it.
    declared: HashSet<String>,
    /// Per-name declaration entries (duplicate/pairing validation).
    entries: std::collections::HashMap<String, Vec<(PrivDeclKind, bool)>>,
    /// Distinct declared names in source order (→ ClassLit.private_names).
    order: Vec<String>,
    /// Private references made lexically in this class (deferred: forward
    /// references to later declarations are legal).
    refs: Vec<String>,
}

/// The duplicate-private-name rule (15.7.1): a name may appear at most twice,
/// and only as a getter/setter pair with matching static-ness.
fn private_kinds_valid(kinds: &[(PrivDeclKind, bool)]) -> bool {
    match kinds.len() {
        0 | 1 => true,
        2 => {
            kinds[0].1 == kinds[1].1
                && matches!(
                    (kinds[0].0, kinds[1].0),
                    (PrivDeclKind::Get, PrivDeclKind::Set) | (PrivDeclKind::Set, PrivDeclKind::Get)
                )
        }
        _ => false,
    }
}

/// Parse one script (a harness include or the test body).
pub fn parse_program(src: &str) -> Result<Program, ParseFail> {
    parse_program_ext(src, false)
}

/// Parse an eval / Function-body script, optionally forcing strict mode. A
/// direct eval inherits its caller's strictness (19.2.1.1), and the Function
/// constructor's assembled body is strict when its calling context is; that
/// strictness must be visible to the PARSER (strict early errors, reserved
/// words) — the parser ORs `force_strict` with any `"use strict"` prologue.
pub fn parse_program_ext(src: &str, force_strict: bool) -> Result<Program, ParseFail> {
    parse_program_inner(src, force_strict).map_err(|e| match e.strip_prefix(EARLY_SYNTAX) {
        Some(m) => ParseFail::EarlySyntaxError(m.to_string()),
        None => ParseFail::OutOfSlice(e),
    })
}

fn parse_program_inner(src: &str, force_strict: bool) -> R<Program> {
    let toks = Lexer::tokenize(src)?;
    let mut p = Parser {
        toks,
        pos: 0,
        depth: 0,
        strict: false,
        in_function: false,
        breakable: 0,
        continuable: 0,
        no_in: false,
        uses_arguments: false,
        in_method: false,
        in_derived_ctor: false,
        forbid_arguments: false,
        in_generator: false,
        in_async: false,
        cover_init_count: 0,
        obj_spread_count: 0,
        proto_single_count: 0,
        proto_dup_count: 0,
        saw_proto_dup: false,
        priv_stack: Vec::new(),
        pending_priv_refs: Vec::new(),
        is_sub: false,
    };
    p.strict = force_strict || p.scan_prologue_strict();
    let body = p.parse_stmt_list_until_eof()?;
    // The parse completed, so no brace form anywhere was a destructuring
    // pattern (all pattern positions refuse as out-of-slice): every recorded
    // duplicate-`__proto__` brace form was a genuine ObjectLiteral, and
    // B.3.1's early error applies.
    if p.proto_dup_count > 0 || p.saw_proto_dup {
        return Err(early_syntax(
            "duplicate `__proto__` data property in object literal",
        ));
    }
    if p.proto_single_count > 0 {
        return Err(
            "object literal `__proto__` data property (sets [[Prototype]], out of slice)"
                .to_string(),
        );
    }
    if p.cover_init_count > 0 {
        // CoverInitializedName outside a destructuring reparse is a pinned
        // SyntaxError.
        return Err(early_syntax(
            "shorthand property initializer outside a destructuring pattern",
        ));
    }
    if p.obj_spread_count > 0 {
        // Object spread in a surviving literal is legal JS but unmodeled (it
        // copies own enumerable properties). Array-literal spread is supported.
        return Err("object spread in a literal (out of slice)".to_string());
    }
    let mut vars = Vec::new();
    collect_vars(&body, &mut vars);
    let funcs = top_level_funcs(&body);
    check_scope(&body, &[], &vars)?;
    Ok(Program {
        strict: p.strict,
        body,
        vars,
        funcs,
    })
}

impl Parser {
    fn cur(&self) -> &Token {
        &self.toks[self.pos]
    }

    fn cur_tok(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn at(&self, p: &str) -> bool {
        matches!(self.cur_tok(), Tok::Punct(q) if *q == p)
    }

    fn at_kw(&self, k: &str) -> bool {
        matches!(self.cur_tok(), Tok::Ident(id) if id == k)
    }

    fn eat(&mut self, p: &str) -> bool {
        if self.at(p) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, k: &str) -> bool {
        if self.at_kw(k) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, p: &str) -> R<()> {
        if self.eat(p) {
            Ok(())
        } else {
            Err(format!("expected `{p}`, found {:?}", self.cur_tok()))
        }
    }

    fn ident_name(&mut self) -> R<String> {
        match self.cur_tok().clone() {
            Tok::Ident(id) | Tok::EscIdent(id) => {
                self.pos += 1;
                Ok(id)
            }
            t => Err(format!("expected identifier, found {t:?}")),
        }
    }

    fn binding_ident(&mut self) -> R<String> {
        let id = self.binding_ident_param()?;
        // A sloppy `arguments` binding (var/let/const/catch/function-name)
        // inside a function aliases/overlays the arguments-object binding:
        // the interplay with the creation condition is out of slice — refuse.
        // (PARAMETERS named `arguments` are exact: they suppress the
        // arguments object per FunctionDeclarationInstantiation step 19, and
        // parse via binding_ident_param.)
        if self.in_function && id == "arguments" {
            return Err("`arguments` binding inside a function (arguments-object overlay out of slice)"
                .to_string());
        }
        Ok(id)
    }

    fn binding_ident_param(&mut self) -> R<String> {
        let escaped = matches!(self.cur_tok(), Tok::EscIdent(_));
        let id = self.ident_name()?;
        // Inside a generator body `yield` is a reserved word: binding it (in
        // any escaped/unescaped form) is a Syntax Error.
        if self.in_generator && id == "yield" {
            return Err(early_syntax("`yield` as a binding in a generator body"));
        }
        // Inside an async body `await` is reserved: binding it (escaped or not)
        // is a Syntax Error.
        if self.in_async && id == "await" {
            return Err(early_syntax("`await` as a binding in an async body"));
        }
        if escaped {
            // Escaped identifiers judge by StringValue against the TRUE
            // ReservedWord set (contextual keywords are legal names). Inside a
            // generator body `yield` is reserved regardless of strictness.
            if is_true_reserved(&id, self.strict) || (self.in_generator && id == "yield") {
                return Err(early_syntax(&format!(
                    "escaped reserved word `{id}` as binding"
                )));
            }
        } else if is_reserved(&id) {
            return Err(format!("reserved word `{id}` as binding"));
        }
        // 13.1.1: BindingIdentifier `eval`/`arguments` in strict code is a
        // Syntax Error — fully specified, so emit it exactly.
        if self.strict && (id == "eval" || id == "arguments") {
            return Err(early_syntax(&format!("`{id}` as binding in strict code")));
        }
        Ok(id)
    }

    fn enter(&mut self) -> R<()> {
        self.depth += 1;
        if self.depth > MAX_PARSE_DEPTH {
            Err("parse depth cap exceeded".to_string())
        } else {
            Ok(())
        }
    }

    fn leave(&mut self) {
        self.depth -= 1;
    }

    /// Directive-prologue scan at the current token position.
    fn scan_prologue_strict(&self) -> bool {
        let mut i = self.pos;
        loop {
            let Tok::Str(u, had_escape) = &self.toks[i].tok else {
                return false;
            };
            let next = &self.toks[i + 1];
            let terminated = match &next.tok {
                Tok::Punct(";") => true,
                Tok::Punct("}") | Tok::Eof => true,
                _ if next.newline_before => true,
                _ => false,
            };
            if !terminated {
                return false;
            }
            if !had_escape && crate::value::units_eq_ascii(u, "use strict") {
                return true;
            }
            i += if matches!(next.tok, Tok::Punct(";")) { 2 } else { 1 };
        }
    }

    // -- statements ---------------------------------------------------------

    fn parse_stmt_list_until_eof(&mut self) -> R<Vec<Stmt>> {
        let mut out = Vec::new();
        while !matches!(self.cur_tok(), Tok::Eof) {
            out.push(self.parse_stmt(true, false)?);
        }
        Ok(out)
    }

    fn parse_stmt_list_until_brace(&mut self, top: bool) -> R<Vec<Stmt>> {
        let mut out = Vec::new();
        while !self.at("}") {
            if matches!(self.cur_tok(), Tok::Eof) {
                return Err("unexpected EOF in block".to_string());
            }
            out.push(self.parse_stmt(top, false)?);
        }
        self.pos += 1;
        Ok(out)
    }

    /// `top` = declarations of functions allowed (script/function top level);
    /// `single` = single-statement position (if/loop body): lexical
    /// declarations and function declarations are refused there.
    fn parse_stmt(&mut self, top: bool, single: bool) -> R<Stmt> {
        self.enter()?;
        let r = self.parse_stmt_inner(top, single);
        self.leave();
        r
    }

    #[allow(clippy::too_many_lines)]
    fn parse_stmt_inner(&mut self, top: bool, single: bool) -> R<Stmt> {
        if self.at("{") {
            self.pos += 1;
            return Ok(Stmt::Block(self.parse_stmt_list_until_brace(false)?));
        }
        if self.eat(";") {
            return Ok(Stmt::Empty);
        }
        let kw_owned = match self.cur_tok() {
            Tok::Ident(id) => Some(id.clone()),
            _ => None,
        };
        if let Some(kw) = kw_owned {
            match kw.as_str() {
                "var" | "let" | "const" => {
                    let kind = match kw.as_str() {
                        "var" => DeclKind::Var,
                        "let" => DeclKind::Let,
                        _ => DeclKind::Const,
                    };
                    if single && kind != DeclKind::Var {
                        return Err("lexical declaration in single-statement position".into());
                    }
                    self.pos += 1;
                    let decls = self.parse_decl_list(kind)?;
                    self.expect_semi()?;
                    return Ok(Stmt::VarDecl { kind, decls });
                }
                "function" => {
                    if !top {
                        return Err(
                            "function declaration outside script/function top level (out of slice)"
                                .into(),
                        );
                    }
                    self.pos += 1;
                    let lit = self.parse_function(true, false)?;
                    return Ok(Stmt::FuncDecl(lit));
                }
                "async" if self.async_heads_function() => {
                    if !top {
                        return Err(
                            "async function declaration outside script/function top level (out of slice)"
                                .into(),
                        );
                    }
                    self.pos += 1; // `async`
                    self.pos += 1; // `function`
                    let lit = self.parse_function(true, true)?;
                    return Ok(Stmt::FuncDecl(lit));
                }
                "if" => {
                    self.pos += 1;
                    self.expect("(")?;
                    let test = self.parse_expression()?;
                    self.expect(")")?;
                    let cons = Box::new(self.parse_stmt(false, true)?);
                    let alt = if self.eat_kw("else") {
                        Some(Box::new(self.parse_stmt(false, true)?))
                    } else {
                        None
                    };
                    return Ok(Stmt::If { test, cons, alt });
                }
                "while" => {
                    self.pos += 1;
                    self.expect("(")?;
                    let test = self.parse_expression()?;
                    self.expect(")")?;
                    let body = Box::new(self.parse_loop_body()?);
                    return Ok(Stmt::While { test, body });
                }
                "do" => {
                    self.pos += 1;
                    let body = Box::new(self.parse_loop_body()?);
                    if !self.eat_kw("while") {
                        return Err("expected `while` after do body".into());
                    }
                    self.expect("(")?;
                    let test = self.parse_expression()?;
                    self.expect(")")?;
                    self.eat(";"); // always insertable after do-while
                    return Ok(Stmt::DoWhile { body, test });
                }
                "for" => {
                    self.pos += 1;
                    return self.parse_for();
                }
                "return" => {
                    if !self.in_function {
                        // `return` is only valid inside a function body; at
                        // script / eval / module top level it is an exact
                        // early SyntaxError with zero engine latitude.
                        return Err(early_syntax("`return` outside a function"));
                    }
                    self.pos += 1;
                    let arg = if self.at(";")
                        || self.at("}")
                        || matches!(self.cur_tok(), Tok::Eof)
                        || self.cur().newline_before
                    {
                        None
                    } else {
                        Some(self.parse_expression()?)
                    };
                    self.expect_semi()?;
                    return Ok(Stmt::Return(arg));
                }
                "throw" => {
                    self.pos += 1;
                    if self.cur().newline_before {
                        return Err("line terminator after `throw`".into());
                    }
                    let arg = self.parse_expression()?;
                    self.expect_semi()?;
                    return Ok(Stmt::Throw(arg));
                }
                "break" | "continue" => {
                    let is_break = kw.as_str() == "break";
                    self.pos += 1;
                    if !self.cur().newline_before {
                        if let Tok::Ident(id) = self.cur_tok() {
                            if !is_reserved(id) {
                                return Err("labeled break/continue (out of slice)".into());
                            }
                        }
                    }
                    // An unlabeled `break`/`continue` with no enclosing
                    // iteration (or switch, for break) is an exact early
                    // SyntaxError (labeled forms were already refused above).
                    if is_break && self.breakable == 0 {
                        return Err(early_syntax("`break` outside a loop or switch"));
                    }
                    if !is_break && self.continuable == 0 {
                        return Err(early_syntax("`continue` outside a loop"));
                    }
                    self.expect_semi()?;
                    return Ok(if is_break { Stmt::Break } else { Stmt::Continue });
                }
                "try" => {
                    self.pos += 1;
                    self.expect("{")?;
                    let block = self.parse_stmt_list_until_brace(false)?;
                    let catch = if self.eat_kw("catch") {
                        let param = if self.eat("(") {
                            let t = self.parse_bind_target()?;
                            self.check_dup_bound(&t)?;
                            self.expect(")")?;
                            Some(t)
                        } else {
                            None
                        };
                        self.expect("{")?;
                        let cbody = self.parse_stmt_list_until_brace(false)?;
                        // 14.15.1: a CatchParameter name that also occurs in
                        // the LexicallyDeclaredNames of the catch Block is a
                        // Syntax Error (var overlap is Annex-B-legal for
                        // simple parameters).
                        if let Some(t) = &param {
                            let mut pnames = Vec::new();
                            t.bound_names(&mut pnames);
                            for s in &cbody {
                                if let Stmt::VarDecl { kind, decls } = s
                                    && *kind != DeclKind::Var
                                {
                                    for (dt, _) in decls {
                                        let mut dn = Vec::new();
                                        dt.bound_names(&mut dn);
                                        if dn.iter().any(|n| pnames.contains(n)) {
                                            return Err(early_syntax(
                                                "catch parameter redeclared lexically in catch block",
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                        Some((param, cbody))
                    } else {
                        None
                    };
                    let finally = if self.eat_kw("finally") {
                        self.expect("{")?;
                        Some(self.parse_stmt_list_until_brace(false)?)
                    } else {
                        None
                    };
                    if catch.is_none() && finally.is_none() {
                        return Err("try without catch/finally".into());
                    }
                    return Ok(Stmt::Try {
                        block,
                        catch,
                        finally,
                    });
                }
                "switch" => {
                    self.pos += 1;
                    return self.parse_switch();
                }
                "class" => {
                    if !top && single {
                        return Err("class declaration in single-statement position".into());
                    }
                    self.pos += 1;
                    let (name, class) = self.parse_class(true)?;
                    return Ok(Stmt::ClassDecl {
                        name: name.expect("declaration has a name"),
                        class,
                    });
                }
                "debugger" | "with" | "import" | "export" => {
                    return Err(format!("`{kw}` statement (out of slice)"));
                }
                // Inside an async body a leading `await` heads an
                // ExpressionStatement (an AwaitExpression, parsed below);
                // elsewhere it is out of slice.
                "await" if !self.in_async => {
                    return Err("`await` statement (out of slice)".into());
                }
                // Inside a generator body a leading `yield` heads a
                // YieldExpression statement (parsed below); elsewhere it is out
                // of slice.
                "yield" if !self.in_generator => {
                    return Err("`yield` statement (out of slice)".into());
                }
                _ => {
                    // Labeled statement? `ident :` — refuse.
                    if !is_reserved(&kw) {
                        if let Tok::Punct(":") = &self.toks[self.pos + 1].tok {
                            return Err("labeled statement (out of slice)".into());
                        }
                    }
                }
            }
        }
        let e = self.parse_expression()?;
        self.expect_semi()?;
        Ok(Stmt::Expr(e))
    }

    fn parse_loop_body(&mut self) -> R<Stmt> {
        self.breakable += 1;
        self.continuable += 1;
        let r = self.parse_stmt(false, true);
        self.breakable -= 1;
        self.continuable -= 1;
        r
    }

    fn parse_decl_list(&mut self, kind: DeclKind) -> R<Vec<(BindTarget, Option<Expr>)>> {
        let mut decls = Vec::new();
        loop {
            let target = self.parse_bind_target()?;
            if kind != DeclKind::Var {
                self.check_dup_bound(&target)?;
            }
            let init = if self.eat("=") {
                let mut e = self.parse_assignment()?;
                if let BindTarget::Name(name) = &target {
                    infer_fn_name(&mut e, name);
                }
                Some(e)
            } else {
                if kind == DeclKind::Const {
                    return Err("const declaration without initializer".into());
                }
                if matches!(target, BindTarget::Pattern(_)) {
                    // 14.3.x: a pattern declarator REQUIRES an initializer.
                    return Err(early_syntax(
                        "destructuring declaration without initializer",
                    ));
                }
                None
            };
            decls.push((target, init));
            if !self.eat(",") {
                return Ok(decls);
            }
        }
    }

    /// Duplicate bound names in one lexical target are a pinned SyntaxError
    /// (lexical declarations, for-in/of lexical heads, catch parameters).
    fn check_dup_bound(&self, t: &BindTarget) -> R<()> {
        let mut ns = Vec::new();
        t.bound_names(&mut ns);
        let mut seen = std::collections::HashSet::new();
        for n in &ns {
            if !seen.insert(n.clone()) {
                return Err(early_syntax(&format!("duplicate bound name `{n}`")));
            }
        }
        Ok(())
    }

    /// A binding target: name or (binding-flavor) pattern.
    fn parse_bind_target(&mut self) -> R<BindTarget> {
        if self.at("[") || self.at("{") {
            Ok(BindTarget::Pattern(Rc::new(self.parse_binding_pattern()?)))
        } else {
            Ok(BindTarget::Name(self.binding_ident()?))
        }
    }

    /// A BindingPattern (8.6.2): leaves are fresh binding names; object rest
    /// targets are names only.
    fn parse_binding_pattern(&mut self) -> R<Pattern> {
        self.enter()?;
        let r = self.parse_binding_pattern_inner();
        self.leave();
        r
    }

    fn parse_binding_pattern_inner(&mut self) -> R<Pattern> {
        if self.eat("[") {
            let mut elems: Vec<Option<PatElem>> = Vec::new();
            let mut rest: Option<Box<Pattern>> = None;
            loop {
                if self.eat("]") {
                    break;
                }
                if self.at(",") {
                    self.pos += 1;
                    elems.push(None); // elision consumes one iterator step
                    continue;
                }
                if self.eat("...") {
                    let p = if self.at("[") || self.at("{") {
                        self.parse_binding_pattern()?
                    } else {
                        Pattern::Ident(self.binding_ident()?)
                    };
                    if self.at("=") {
                        return Err(early_syntax("rest element with initializer"));
                    }
                    rest = Some(Box::new(p));
                    if !self.eat("]") {
                        return Err(early_syntax("rest element must be last"));
                    }
                    break;
                }
                let pat = if self.at("[") || self.at("{") {
                    self.parse_binding_pattern()?
                } else {
                    Pattern::Ident(self.binding_ident()?)
                };
                let default = if self.eat("=") {
                    Some(Rc::new(self.parse_assignment_in()?))
                } else {
                    None
                };
                elems.push(Some(PatElem { pat, default }));
                if self.eat("]") {
                    break;
                }
                self.expect(",")?;
            }
            return Ok(Pattern::Array { elems, rest });
        }
        self.expect("{")?;
        let mut props: Vec<(ObjKey, PatElem)> = Vec::new();
        let mut rest: Option<Box<Pattern>> = None;
        loop {
            if self.eat("}") {
                break;
            }
            if self.eat("...") {
                // BindingRestProperty: BindingIdentifier only.
                let n = self.binding_ident()?;
                rest = Some(Box::new(Pattern::Ident(n)));
                if !self.eat("}") {
                    return Err(early_syntax("object rest must be last"));
                }
                break;
            }
            let (key, ident_key) = self.parse_obj_key()?;
            let elem = if self.eat(":") {
                let pat = if self.at("[") || self.at("{") {
                    self.parse_binding_pattern()?
                } else {
                    Pattern::Ident(self.binding_ident()?)
                };
                let default = if self.eat("=") {
                    Some(Rc::new(self.parse_assignment_in()?))
                } else {
                    None
                };
                PatElem { pat, default }
            } else {
                // Shorthand (with optional default).
                let Some(id) = ident_key else {
                    return Err("bad object-pattern shorthand key".into());
                };
                if is_reserved(&id) {
                    return Err(format!("reserved word `{id}` in object pattern"));
                }
                if self.strict && (id == "eval" || id == "arguments") {
                    return Err(early_syntax(&format!("`{id}` as binding in strict code")));
                }
                if self.in_function && id == "arguments" {
                    return Err(
                        "`arguments` binding inside a function (arguments-object overlay out of slice)"
                            .into(),
                    );
                }
                let default = if self.eat("=") {
                    Some(Rc::new(self.parse_assignment_in()?))
                } else {
                    None
                };
                PatElem {
                    pat: Pattern::Ident(id),
                    default,
                }
            };
            props.push((key, elem));
            if self.eat("}") {
                break;
            }
            self.expect(",")?;
        }
        Ok(Pattern::Object { props, rest })
    }

    /// The for-in/for-of assignment target from a parsed head expression:
    /// a simple reference (Ident/Member), or an object/array literal that
    /// reparses as an AssignmentPattern.
    fn forinof_target(&mut self, e: Expr) -> R<ForInOfLeft> {
        match &e {
            Expr::Ident(id) => {
                if self.strict && (id == "eval" || id == "arguments") {
                    return Err(early_syntax(&format!(
                        "for-in/of assignment to `{id}` in strict code"
                    )));
                }
                Ok(ForInOfLeft::Target(e))
            }
            Expr::Member { .. } | Expr::SuperMember { .. } => Ok(ForInOfLeft::Target(e)),
            Expr::Paren(inner) if matches!(**inner, Expr::Ident(_) | Expr::Member { .. }) => {
                Ok(ForInOfLeft::Target((**inner).clone()))
            }
            Expr::Object(_) | Expr::Array(_) => {
                let pat = self.expr_to_pattern(e)?;
                Ok(ForInOfLeft::TargetPattern(Rc::new(pat)))
            }
            _ => Err("for-in/of target is not a simple reference (out of slice)".into()),
        }
    }

    /// Common tail of a for-in / for-of statement after the keyword. The
    /// for-in head is a full Expression (comma legal); the for-of head is a
    /// single AssignmentExpression — a following comma is a pinned Syntax
    /// Error (13.7.5: `for ( ... of AssignmentExpression )`).
    fn parse_forinof_tail(&mut self, left: ForInOfLeft, is_in: bool) -> R<Stmt> {
        self.pos += 1; // the `in` / `of` keyword
        let head = if is_in {
            self.parse_expression_in()?
        } else {
            let e = self.parse_assignment_in()?;
            if self.at(",") {
                return Err(early_syntax(
                    "comma expression in the for-of head AssignmentExpression position",
                ));
            }
            e
        };
        self.expect(")")?;
        let body = Box::new(self.parse_loop_body()?);
        // 14.7.1.1: the ForDeclaration's bound name may not appear in the
        // VarDeclaredNames of the body (refused conservatively), nor be
        // `let`.
        if let ForInOfLeft::Lex(t, _) = &left {
            let mut names = Vec::new();
            t.bound_names(&mut names);
            let mut body_vars = Vec::new();
            collect_vars_stmt(&body, &mut body_vars);
            for n in &names {
                if body_vars.contains(n) {
                    return Err(format!(
                        "for-in/of lexical name `{n}` also var-declared in body (refused)"
                    ));
                }
            }
        }
        Ok(if is_in {
            Stmt::ForIn { left, obj: head, body }
        } else {
            Stmt::ForOf {
                left,
                expr: head,
                body,
            }
        })
    }

    #[allow(clippy::too_many_lines)]
    fn parse_for(&mut self) -> R<Stmt> {
        self.expect("(")?;
        let init = if self.eat(";") {
            None
        } else if self.at_kw("let") || self.at_kw("const") {
            let is_const = self.at_kw("const");
            self.pos += 1;
            let target = self.parse_bind_target()?;
            self.check_dup_bound(&target)?;
            if self.at_kw("in") {
                return self.parse_forinof_tail(ForInOfLeft::Lex(target, is_const), true);
            }
            if self.at_kw("of") {
                return self.parse_forinof_tail(ForInOfLeft::Lex(target, is_const), false);
            }
            // Classic lexical for-head: `for (let/const a = x, b = y; ...)`.
            let saved = self.no_in;
            self.no_in = true;
            let decls = (|p: &mut Parser| -> R<Vec<(BindTarget, Option<Expr>)>> {
                let mut decls: Vec<(BindTarget, Option<Expr>)> = Vec::new();
                let mut cur = target;
                loop {
                    let init = if p.eat("=") {
                        let mut e = p.parse_assignment()?;
                        if let BindTarget::Name(n) = &cur {
                            infer_fn_name(&mut e, n);
                        }
                        Some(e)
                    } else {
                        if is_const {
                            return Err("const declaration without initializer".into());
                        }
                        if matches!(cur, BindTarget::Pattern(_)) {
                            return Err(early_syntax(
                                "destructuring declaration without initializer",
                            ));
                        }
                        None
                    };
                    p.check_dup_bound(&cur)?;
                    let mut new_names = Vec::new();
                    cur.bound_names(&mut new_names);
                    for (t, _) in &decls {
                        let mut have = Vec::new();
                        t.bound_names(&mut have);
                        if new_names.iter().any(|n| have.contains(n)) {
                            return Err("duplicate lexical for-head name".into());
                        }
                    }
                    decls.push((cur, init));
                    if !p.eat(",") {
                        return Ok(decls);
                    }
                    cur = p.parse_bind_target()?;
                }
            })(self);
            self.no_in = saved;
            let decls = decls?;
            self.expect(";")?;
            Some(crate::ast::ForInit::Lex { is_const, decls })
        } else if self.eat_kw("var") {
            // The first declarator may be a bare pattern followed by in/of.
            let first = self.parse_bind_target()?;
            if (self.at_kw("in") || self.at_kw("of")) && !self.at("=") {
                let is_in = self.at_kw("in");
                return self.parse_forinof_tail(ForInOfLeft::Var(first), is_in);
            }
            let saved = self.no_in;
            self.no_in = true;
            let decls = (|p: &mut Parser| -> R<Vec<(BindTarget, Option<Expr>)>> {
                let mut decls: Vec<(BindTarget, Option<Expr>)> = Vec::new();
                let mut cur = first;
                loop {
                    let init = if p.eat("=") {
                        let mut e = p.parse_assignment()?;
                        if let BindTarget::Name(n) = &cur {
                            infer_fn_name(&mut e, n);
                        }
                        Some(e)
                    } else {
                        if matches!(cur, BindTarget::Pattern(_)) {
                            return Err(early_syntax(
                                "destructuring declaration without initializer",
                            ));
                        }
                        None
                    };
                    decls.push((cur, init));
                    if !p.eat(",") {
                        return Ok(decls);
                    }
                    cur = p.parse_bind_target()?;
                }
            })(self);
            self.no_in = saved;
            let decls = decls?;
            if self.at_kw("in") || self.at_kw("of") {
                let is_in = self.at_kw("in");
                if decls.len() != 1 || decls[0].1.is_some() {
                    return Err(
                        "for-in/of var head with initializer or multiple declarators (out of slice)"
                            .into(),
                    );
                }
                return self
                    .parse_forinof_tail(ForInOfLeft::Var(decls[0].0.clone()), is_in);
            }
            self.expect(";")?;
            Some(crate::ast::ForInit::Var(decls))
        } else {
            // 14.7.5: `for ( [lookahead ∉ { let [, async of }] LHS of ... )` —
            // a bare `async` token before `of` is a pinned Syntax Error
            // (unless it opens an `async of => ...` async arrow, which is
            // out of slice and refuses below).
            if self.at_kw("async")
                && matches!(&self.toks[self.pos + 1].tok, Tok::Ident(id) if id == "of")
                && !matches!(&self.toks[self.pos + 2].tok, Tok::Punct("=>"))
            {
                return Err(early_syntax("`async of` in a for-of head"));
            }
            let saved = self.no_in;
            self.no_in = true;
            let e = self.parse_expression();
            self.no_in = saved;
            let e = e?;
            if self.at_kw("in") || self.at_kw("of") {
                let is_in = self.at_kw("in");
                let left = self.forinof_target(e)?;
                return self.parse_forinof_tail(left, is_in);
            }
            self.expect(";")?;
            Some(crate::ast::ForInit::Expr(e))
        };
        let test = if self.at(";") {
            None
        } else {
            Some(self.parse_expression()?)
        };
        self.expect(";")?;
        let update = if self.at(")") {
            None
        } else {
            Some(self.parse_expression()?)
        };
        self.expect(")")?;
        let body = Box::new(self.parse_loop_body()?);
        // 14.7.4.1: a lexical for-head name may not appear in the body's
        // VarDeclaredNames (refused conservatively rather than judged).
        if let Some(crate::ast::ForInit::Lex { decls, .. }) = &init {
            let mut body_vars = Vec::new();
            collect_vars_stmt(&body, &mut body_vars);
            for (t, _) in decls {
                let mut ns = Vec::new();
                t.bound_names(&mut ns);
                for n in &ns {
                    if body_vars.contains(n) {
                        return Err(format!(
                            "for-head lexical name `{n}` also var-declared in body (refused)"
                        ));
                    }
                }
            }
        }
        Ok(Stmt::For {
            init,
            test,
            update,
            body,
        })
    }

    fn parse_switch(&mut self) -> R<Stmt> {
        self.expect("(")?;
        let disc = self.parse_expression()?;
        self.expect(")")?;
        self.expect("{")?;
        let mut cases: Vec<(Option<Expr>, Vec<Stmt>)> = Vec::new();
        let mut seen_default = false;
        self.breakable += 1;
        let r = (|| -> R<()> {
            while !self.eat("}") {
                let test = if self.eat_kw("case") {
                    let t = self.parse_expression()?;
                    Some(t)
                } else if self.eat_kw("default") {
                    if seen_default {
                        return Err("duplicate `default` clause".into());
                    }
                    seen_default = true;
                    None
                } else {
                    return Err(format!("expected case/default, found {:?}", self.cur_tok()));
                };
                self.expect(":")?;
                let mut stmts = Vec::new();
                while !self.at("}") && !self.at_kw("case") && !self.at_kw("default") {
                    stmts.push(self.parse_stmt(false, false)?);
                }
                cases.push((test, stmts));
            }
            Ok(())
        })();
        self.breakable -= 1;
        r?;
        Ok(Stmt::Switch { disc, cases })
    }

    fn parse_function(&mut self, is_decl: bool, is_async: bool) -> R<Rc<FuncLit>> {
        let is_generator = self.eat("*");
        if is_async && is_generator {
            return Err("async generator function (async generators out of slice)".to_string());
        }
        // The BindingIdentifier's [Yield]: a DECLARATION name (generator or
        // not) inherits the enclosing context's [Yield] — it binds in the
        // OUTER scope — so `function* yield() {}` at script top level is legal;
        // an EXPRESSION name is [+Yield] for a generator (it may self-refer
        // inside the generator) and [~Yield] for a plain function.
        let name_yield = if is_decl { self.in_generator } else { is_generator };
        let saved_ig = self.in_generator;
        self.in_generator = name_yield;
        let name = if matches!(self.cur_tok(), Tok::Ident(_) | Tok::EscIdent(_)) {
            Some(self.binding_ident()?)
        } else {
            None
        };
        self.in_generator = saved_ig;
        if is_decl && name.is_none() {
            // A `function` at statement level without a name is a pinned
            // Syntax Error in scripts (only `export default` admits one, and
            // modules are out of slice before this point).
            return Err(early_syntax("anonymous function declaration"));
        }
        // FormalParameters[?Yield]: a GENERATOR's own parameters are [+Yield]
        // (a YieldExpression there is an early error — flagged in
        // check_param_default), while a NON-generator function's parameters
        // are [~Yield] regardless of the enclosing context — so `yield` in
        // them is an ordinary IdentifierReference (legal sloppy, a SyntaxError
        // in strict code), never inherited as a YieldExpression from an outer
        // generator.
        let saved_pig = self.in_generator;
        self.in_generator = is_generator;
        let params_result = self.parse_params();
        self.in_generator = saved_pig;
        let (params, rest_param, simple_params) = params_result?;
        self.expect("{")?;
        let has_directive = self.scan_prologue_strict();
        let strict = self.strict || has_directive;
        if has_directive && !simple_params {
            // 15.2.1: a 'use strict' DIRECTIVE with a non-simple parameter
            // list is a Syntax Error — even in already-strict code.
            return Err(early_syntax(
                "'use strict' directive in a function with a non-simple parameter list",
            ));
        }
        let saved = (
            self.strict,
            self.in_function,
            self.breakable,
            self.continuable,
            self.no_in,
            self.uses_arguments,
            self.in_method,
            self.in_derived_ctor,
            self.forbid_arguments,
            self.in_generator,
        );
        self.strict = strict;
        self.in_function = true;
        self.breakable = 0;
        self.continuable = 0;
        self.no_in = false;
        self.uses_arguments = false;
        self.in_method = false;
        self.in_derived_ctor = false;
        self.forbid_arguments = false;
        self.in_generator = is_generator;
        let saved_async = self.in_async;
        self.in_async = is_async;
        let body = self.parse_stmt_list_until_brace(true);
        let uses_arguments = self.uses_arguments;
        self.in_async = saved_async;
        (
            self.strict,
            self.in_function,
            self.breakable,
            self.continuable,
            self.no_in,
            self.uses_arguments,
            self.in_method,
            self.in_derived_ctor,
            self.forbid_arguments,
            self.in_generator,
        ) = saved;
        let body = body?;
        // 15.1.1 / 13.1.1: once the body's directive prologue is known, a
        // strict function whose NAME or any PARAMETER is `eval`/`arguments`
        // is a Syntax Error — retroactively (the identifiers were parsed
        // under the outer, possibly sloppy, context).
        if strict {
            if let Some(n) = &name
                && (n == "eval" || n == "arguments")
            {
                return Err(early_syntax(&format!("`{n}` as strict function name")));
            }
            for p in param_names(&params, &rest_param) {
                if p == "eval" || p == "arguments" {
                    return Err(early_syntax(&format!(
                        "`{p}` as strict function parameter"
                    )));
                }
            }
        }
        let mut vars = Vec::new();
        collect_vars(&body, &mut vars);
        let funcs = top_level_funcs(&body);
        let pnames = param_names(&params, &rest_param);
        check_scope(&body, &pnames, &vars)?;
        // FunctionDeclarationInstantiation step 19: a parameter named
        // `arguments` suppresses the arguments object; the identifier then
        // resolves to the parameter binding.
        let uses_arguments = uses_arguments && !pnames.iter().any(|p| p == "arguments");
        Ok(Rc::new(FuncLit {
            name,
            inferred_name: false,
            params,
            rest_param,
            simple_params,
            body,
            strict,
            vars,
            funcs,
            uses_arguments,
            is_method: false,
            is_arrow: false,
            is_generator,
            is_async,
        }))
    }

    /// A formal parameter list after `(`: names, patterns, defaults (with
    /// the slice restriction: no function/class literals and no `arguments`
    /// inside parameter initializers — the separate parameter scope those
    /// need is out of slice), and a rest parameter.
    fn parse_params(&mut self) -> R<(Vec<Param>, Option<BindTarget>, bool)> {
        self.expect("(")?;
        let mut params: Vec<Param> = Vec::new();
        let mut rest: Option<BindTarget> = None;
        let mut simple = true;
        if !self.eat(")") {
            loop {
                if self.eat("...") {
                    simple = false;
                    let t = self.parse_param_target()?;
                    if self.at("=") {
                        return Err(early_syntax("rest parameter with initializer"));
                    }
                    rest = Some(t);
                    if !self.eat(")") {
                        return Err(early_syntax("rest parameter must be last"));
                    }
                    break;
                }
                let target = self.parse_param_target()?;
                if matches!(target, BindTarget::Pattern(_)) {
                    simple = false;
                }
                let default = if self.eat("=") {
                    simple = false;
                    let e = self.parse_assignment_in()?;
                    self.check_param_default(&e)?;
                    Some(Rc::new(e))
                } else {
                    None
                };
                params.push(Param { target, default });
                if self.eat(")") {
                    break;
                }
                self.expect(",")?;
                if self.eat(")") {
                    break; // trailing comma
                }
            }
        }
        // Duplicate bound names: legal only for simple sloppy lists, which
        // the existing model refuses anyway — refuse all duplicates.
        let mut names: Vec<String> = Vec::new();
        for p in &params {
            p.target.bound_names(&mut names);
        }
        if let Some(r) = &rest {
            r.bound_names(&mut names);
        }
        let mut seen = std::collections::HashSet::new();
        for n in &names {
            if !seen.insert(n.clone()) {
                return Err("duplicate parameter (out of slice)".into());
            }
        }
        Ok((params, rest, simple))
    }

    fn parse_param_target(&mut self) -> R<BindTarget> {
        if self.at("[") || self.at("{") {
            Ok(BindTarget::Pattern(Rc::new(self.parse_binding_pattern()?)))
        } else {
            Ok(BindTarget::Name(self.binding_ident_param()?))
        }
    }

    /// Slice restriction on parameter initializers: closures (function/
    /// class/arrow literals) and `arguments` would observe the separate
    /// parameter scope — refuse them.
    fn check_param_default(&self, e: &Expr) -> R<()> {
        let mut found: Option<String> = None;
        walk_expr(e, &mut |x| match x {
            Expr::Yield { .. } => {
                // A YieldExpression is only ever produced inside a [+Yield]
                // parameter list (a generator's own parameters, or an arrow's
                // parameters lexically inside a generator). "It is a Syntax
                // Error if [Arrow]FormalParameters Contains YieldExpression."
                // This is a fully-specified early error — pin it (overriding
                // any out-of-slice refusal recorded for the same default).
                found = Some(early_syntax("YieldExpression in formal parameters"));
            }
            Expr::Function(_) | Expr::Arrow(_) | Expr::Class(_) => {
                if found.is_none() {
                    found = Some(
                        "closure in a parameter initializer (parameter scope out of slice)"
                            .to_string(),
                    );
                }
            }
            Expr::Ident(n) if n == "arguments" => {
                if found.is_none() {
                    found =
                        Some("`arguments` in a parameter initializer (out of slice)".to_string());
                }
            }
            _ => {}
        });
        match found {
            Some(m) => Err(m),
            None => Ok(()),
        }
    }

    /// `super.x` outside any method context is a pinned SyntaxError.
    fn check_super_member(&self) -> R<()> {
        if self.in_method {
            return Ok(());
        }
        Err(early_syntax("`super` property outside a method"))
    }

    /// Record a private reference `#name` for AllPrivateIdentifiersValid: it is
    /// deferred (forward references are legal) to the current class's scope, or
    /// bubbled to the parent (template sub), or — with no enclosing class — a
    /// pinned SyntaxError (`#x` outside a class body).
    fn record_priv_ref(&mut self, name: String) -> R<()> {
        if let Some(top) = self.priv_stack.last_mut() {
            top.refs.push(name);
            Ok(())
        } else if self.is_sub {
            self.pending_priv_refs.push(name);
            Ok(())
        } else {
            Err(early_syntax(&format!(
                "private name `#{name}` outside a class body"
            )))
        }
    }

    /// Declare a private class element (15.7.1 duplicate/pairing early error).
    fn declare_private(&mut self, name: &str, kind: PrivDeclKind, is_static: bool) -> R<()> {
        if name == "constructor" {
            return Err(early_syntax("private class element named `#constructor`"));
        }
        let top = self
            .priv_stack
            .last_mut()
            .expect("private declaration inside a class scope");
        let mut kinds = top.entries.get(name).cloned().unwrap_or_default();
        let first = kinds.is_empty();
        kinds.push((kind, is_static));
        if !private_kinds_valid(&kinds) {
            return Err(early_syntax(&format!("duplicate private name `#{name}`")));
        }
        if first {
            top.order.push(name.to_string());
            top.declared.insert(name.to_string());
        }
        top.entries.insert(name.to_string(), kinds);
        Ok(())
    }

    // -- classes ------------------------------------------------------------

    /// Parse a class after the `class` keyword. Class code (name, heritage,
    /// body) is strict.
    fn parse_class(&mut self, is_decl: bool) -> R<(Option<String>, Rc<ClassLit>)> {
        let saved_strict = self.strict;
        self.strict = true;
        let r = self.parse_class_inner(is_decl);
        self.strict = saved_strict;
        r
    }

    #[allow(clippy::too_many_lines)]
    fn parse_class_inner(&mut self, is_decl: bool) -> R<(Option<String>, Rc<ClassLit>)> {
        let name = if matches!(self.cur_tok(), Tok::Ident(_) | Tok::EscIdent(_))
            && !self.at_kw("extends")
        {
            Some(self.binding_ident()?)
        } else {
            None
        };
        if is_decl && name.is_none() {
            return Err(early_syntax("anonymous class declaration"));
        }
        // ClassHeritage evaluates in the OUTER PrivateEnvironment
        // (ClassDefinitionEvaluation NOTE: "The running execution context's
        // PrivateEnvironment is outerPrivateEnvironment when evaluating
        // ClassHeritage"). AllPrivateIdentifiersValid checks ClassHeritage
        // with the outer names only — the class's own `#name`s are NOT in
        // scope there. So the class's PrivateEnvironment is deliberately NOT
        // yet on the stack while the heritage (including any nested class
        // expression it contains) is parsed: a `#name` used in the heritage
        // resolves against an ENCLOSING class, or — with none — is an
        // undeclared-private early SyntaxError.
        let heritage = if self.eat_kw("extends") {
            // ClassHeritage is a LeftHandSideExpression: a (non-
            // parenthesized) arrow — including an async arrow (`async () =>` /
            // `async x =>`) — is a pinned SyntaxError. An async FUNCTION
            // expression, by contrast, IS a LeftHandSideExpression and parses
            // normally (its non-constructor status is a runtime TypeError).
            if self.at("(") && self.paren_starts_arrow() {
                return Err(early_syntax("arrow function as class heritage"));
            }
            if self.async_heads_arrow() {
                return Err(early_syntax("async arrow function as class heritage"));
            }
            if matches!(self.cur_tok(), Tok::Ident(id) if !is_reserved(id))
                && matches!(self.toks[self.pos + 1].tok, Tok::Punct("=>"))
                && !self.toks[self.pos + 1].newline_before
            {
                return Err(early_syntax("arrow function as class heritage"));
            }
            Some(Box::new(self.parse_lhs()?))
        } else {
            None
        };
        // Now the class's PrivateEnvironment becomes active for the ClassBody:
        // computed keys, field initializers, methods, the constructor, and
        // `#x in obj` all resolve against it (parented on the enclosing
        // environments).
        self.priv_stack.push(PrivScope {
            declared: HashSet::new(),
            entries: std::collections::HashMap::new(),
            order: Vec::new(),
            refs: Vec::new(),
        });
        let derived = heritage.is_some();
        self.expect("{")?;
        let mut ctor: Option<Rc<FuncLit>> = None;
        let mut members: Vec<ClassMember> = Vec::new();
        loop {
            if self.eat("}") {
                break;
            }
            if self.eat(";") {
                continue;
            }
            // `static` is a modifier unless it heads a member of its own
            // (`static() {}`, `static = 1`, `static;`).
            let stat = self.at_kw("static")
                && !matches!(self.toks[self.pos + 1].tok, Tok::Punct("(" | "=" | ";" | "}"));
            if stat {
                self.pos += 1;
                if self.at("{") {
                    return Err("static initialization block (out of slice)".into());
                }
            }
            // `async` heads an async method (`async m(){}` / `async *m(){}`)
            // when it is not itself the member name (`async(){}`, `async = 1`,
            // `async;`, `async}`) and no LineTerminator follows (the
            // [no LineTerminator here] restriction — `async \n m(){}` is a
            // field named `async`). `async *m(){}` is an async generator
            // method (refused in parse_method_fn).
            let is_async = self.at_kw("async")
                && !matches!(self.toks[self.pos + 1].tok, Tok::Punct("(" | "=" | ";" | "}"))
                && !self.toks[self.pos + 1].newline_before;
            if is_async {
                self.pos += 1; // consume `async`
            }
            let is_gen = self.eat("*");
            // Accessor lookahead: get/set followed by a property name. A `*`
            // marker forces a generator method — `*get(){}` names the method
            // "get", it is not an accessor. An `async` prefix forbids the
            // accessor form (`async get(){}` is an async method named `get`).
            let mk = if !is_async
                && !is_gen
                && (self.at_kw("get") || self.at_kw("set"))
                && matches!(
                    self.toks[self.pos + 1].tok,
                    Tok::Ident(_)
                        | Tok::EscIdent(_)
                        | Tok::PrivateIdent(_)
                        | Tok::Str(..)
                        | Tok::Num(_)
                        | Tok::BigInt(_)
                        | Tok::Punct("[")
                ) {
                let is_get = self.at_kw("get");
                self.pos += 1;
                if is_get { MethodKind::Get } else { MethodKind::Set }
            } else {
                MethodKind::Normal
            };
            let key = self.parse_class_key()?;
            // The bare private name declared by this member (if any).
            let priv_name = match &key {
                ClassKey::Private(n) => Some(n.clone()),
                _ => None,
            };
            let fixed_is = |k: &ClassKey, s: &str| {
                matches!(k, ClassKey::Fixed(u) if crate::value::units_eq_ascii(u, s))
            };
            if is_gen && !self.at("(") {
                // A `*`-prefixed class member is a GeneratorMethod and MUST
                // carry a parameter list; `class C { *x }` / `*x = 1` (no
                // `(...)`) is a pinned SyntaxError — there is no generator
                // FieldDefinition.
                return Err(early_syntax(
                    "`*` generator prefix without a method parameter list in class body",
                ));
            }
            if is_async && !self.at("(") {
                // An `async`-prefixed class member is an async method and MUST
                // carry a parameter list; there is no async FieldDefinition.
                return Err(early_syntax(
                    "`async` prefix without a method parameter list in class body",
                ));
            }
            if self.at("(") {
                // MethodDefinition.
                if stat && fixed_is(&key, "prototype") {
                    return Err(early_syntax("static class member named `prototype`"));
                }
                if fixed_is(&key, "constructor") {
                    if stat {
                        // `static constructor() {}` is an ordinary static
                        // method (may be async).
                    } else if mk != MethodKind::Normal || is_gen || is_async {
                        return Err(early_syntax(
                            "async/accessor/generator class member named `constructor`",
                        ));
                    } else {
                        if ctor.is_some() {
                            return Err(early_syntax("duplicate `constructor`"));
                        }
                        let lit = self.parse_method_fn(
                            MethodKind::Normal,
                            false,
                            derived,
                            true,
                            false,
                            false,
                        )?;
                        ctor = Some(lit);
                        continue;
                    }
                }
                if let Some(n) = &priv_name {
                    let kind = match mk {
                        MethodKind::Get => PrivDeclKind::Get,
                        MethodKind::Set => PrivDeclKind::Set,
                        MethodKind::Normal => PrivDeclKind::Method,
                    };
                    self.declare_private(n, kind, stat)?;
                }
                let lit = self.parse_method_fn(mk, true, derived, true, is_gen, is_async)?;
                members.push(ClassMember::Method {
                    stat,
                    key,
                    mk,
                    lit,
                });
            } else {
                // FieldDefinition.
                if mk != MethodKind::Normal {
                    return Err(format!(
                        "expected `(` after get/set class member, found {:?}",
                        self.cur_tok()
                    ));
                }
                if fixed_is(&key, "constructor") {
                    return Err(early_syntax("class field named `constructor`"));
                }
                if stat && fixed_is(&key, "prototype") {
                    return Err(early_syntax("static class member named `prototype`"));
                }
                if let Some(n) = &priv_name {
                    self.declare_private(n, PrivDeclKind::Field, stat)?;
                }
                let init = if self.eat("=") {
                    let saved = (self.in_method, self.in_derived_ctor, self.forbid_arguments);
                    self.in_method = true; // super.x is legal in field inits
                    self.in_derived_ctor = false;
                    self.forbid_arguments = true;
                    let e = self.parse_assignment_in();
                    (self.in_method, self.in_derived_ctor, self.forbid_arguments) = saved;
                    Some(Rc::new(e?))
                } else {
                    None
                };
                self.expect_semi()?;
                members.push(ClassMember::Field { stat, key, init });
            }
        }
        // Close the class scope: distinct private names become the ClassLit's
        // list; any reference not declared here bubbles to the enclosing class
        // (nested-class resolution), or — with none — is an undeclared-private
        // SyntaxError.
        let scope = self.priv_stack.pop().expect("pushed at class start");
        let private_names = scope.order;
        for r in scope.refs {
            if !scope.declared.contains(&r) {
                self.record_priv_ref(r)?;
            }
        }
        Ok((
            name.clone(),
            Rc::new(ClassLit {
                name,
                inferred_name: std::cell::RefCell::new(None),
                heritage,
                ctor,
                members,
                private_names,
            }),
        ))
    }

    /// A class member key: identifier-name (any, including reserved words),
    /// string, number, or a computed expression.
    fn parse_class_key(&mut self) -> R<ClassKey> {
        match self.cur_tok().clone() {
            Tok::PrivateIdent(name) => {
                self.pos += 1;
                Ok(ClassKey::Private(name))
            }
            Tok::Ident(id) | Tok::EscIdent(id) => {
                self.pos += 1;
                Ok(ClassKey::Fixed(units_from_str(&id)))
            }
            Tok::Str(u, _) => {
                self.pos += 1;
                Ok(ClassKey::Fixed(u))
            }
            Tok::Num(n) => {
                self.pos += 1;
                Ok(ClassKey::Fixed(units_from_str(
                    &crate::number::js_number_to_string(n),
                )))
            }
            Tok::BigInt(b) => {
                self.pos += 1;
                Ok(ClassKey::Fixed(units_from_str(&b.to_str_radix(10))))
            }
            Tok::Punct("[") => {
                self.pos += 1;
                let e = self.parse_assignment_in()?;
                self.expect("]")?;
                Ok(ClassKey::Computed(Box::new(e)))
            }
            t => Err(format!("bad class member key {t:?}")),
        }
    }

    /// A class method / accessor / constructor function: params + strict
    /// body, with the super flags set for the body.
    #[allow(clippy::too_many_arguments)]
    fn parse_method_fn(
        &mut self,
        mk: MethodKind,
        is_method: bool,
        derived_ctor_ok: bool,
        force_strict: bool,
        is_generator: bool,
        is_async: bool,
    ) -> R<Rc<FuncLit>> {
        // An async generator method (`async *m(){}`) needs the combined
        // yield+await machine — out of slice; refuse cleanly.
        if is_async && is_generator {
            return Err("async generator method (async generators out of slice)".to_string());
        }
        // Parameter initializers are method code: `super.x` (and `super()`
        // in a derived constructor) is legal there, with the method's
        // [[HomeObject]] at runtime.
        let saved_m = (self.in_method, self.in_derived_ctor, self.in_generator);
        self.in_method = true;
        self.in_derived_ctor = !is_method && derived_ctor_ok;
        // A GeneratorMethod's UniqueFormalParameters are [+Yield] (a
        // YieldExpression there is an early error); a regular / get / set
        // method's parameters are [~Yield].
        self.in_generator = is_generator;
        let params_r = self.parse_params();
        (self.in_method, self.in_derived_ctor, self.in_generator) = saved_m;
        let (params, rest_param, simple_params) = params_r?;
        match mk {
            MethodKind::Get if !params.is_empty() || rest_param.is_some() => {
                return Err(early_syntax("getter with parameters"));
            }
            MethodKind::Set if params.len() != 1 || rest_param.is_some() => {
                return Err(early_syntax("setter without exactly one non-rest parameter"));
            }
            _ => {}
        }
        self.expect("{")?;
        let has_directive = self.scan_prologue_strict();
        let strict = force_strict || self.strict || has_directive;
        if has_directive && !simple_params {
            return Err(early_syntax(
                "'use strict' directive in a method with a non-simple parameter list",
            ));
        }
        let saved = (
            self.strict,
            self.in_function,
            self.breakable,
            self.continuable,
            self.no_in,
            self.uses_arguments,
            self.in_method,
            self.in_derived_ctor,
            self.forbid_arguments,
            self.in_generator,
        );
        self.strict = strict;
        self.in_function = true;
        self.breakable = 0;
        self.continuable = 0;
        self.no_in = false;
        self.uses_arguments = false;
        self.in_method = true;
        self.in_derived_ctor = !is_method && derived_ctor_ok;
        self.forbid_arguments = false;
        self.in_generator = is_generator;
        // Inside an async method body `await` heads an AwaitExpression, exactly
        // as in an async function body (an async method IS an async function
        // with a [[HomeObject]]).
        let saved_async = self.in_async;
        self.in_async = is_async;
        let body = self.parse_stmt_list_until_brace(true);
        let uses_arguments = self.uses_arguments;
        self.in_async = saved_async;
        (
            self.strict,
            self.in_function,
            self.breakable,
            self.continuable,
            self.no_in,
            self.uses_arguments,
            self.in_method,
            self.in_derived_ctor,
            self.forbid_arguments,
            self.in_generator,
        ) = saved;
        let body = body?;
        // Retroactive strict `eval`/`arguments` parameter early error (the
        // params may have parsed under a sloppy outer context).
        let pnames = param_names(&params, &rest_param);
        if strict {
            for p in &pnames {
                if p == "eval" || p == "arguments" {
                    return Err(early_syntax(&format!(
                        "`{p}` as strict method parameter"
                    )));
                }
            }
        }
        let mut vars = Vec::new();
        collect_vars(&body, &mut vars);
        let funcs = top_level_funcs(&body);
        check_scope(&body, &pnames, &vars)?;
        let uses_arguments = uses_arguments && !pnames.iter().any(|p| p == "arguments");
        Ok(Rc::new(FuncLit {
            name: None, // the exact name prop is set at definition time
            inferred_name: true,
            params,
            rest_param,
            simple_params,
            body,
            strict,
            vars,
            funcs,
            uses_arguments,
            is_method,
            is_arrow: false,
            is_generator,
            is_async,
        }))
    }

    /// Reparse a parsed Object/Array LITERAL as an AssignmentPattern
    /// (13.15.1 cover grammar), decrementing the cover counters it consumed.
    #[allow(clippy::too_many_lines)]
    fn expr_to_pattern(&mut self, e: Expr) -> R<Pattern> {
        match e {
            Expr::Ident(id) => {
                if self.strict && (id == "eval" || id == "arguments") {
                    return Err(early_syntax(&format!(
                        "assignment to `{id}` in strict code"
                    )));
                }
                Ok(Pattern::Ident(id))
            }
            Expr::Member { .. } | Expr::SuperMember { .. } => Ok(Pattern::Target(Rc::new(e))),
            Expr::Array(elems) => {
                let mut out: Vec<Option<PatElem>> = Vec::new();
                let mut rest: Option<Box<Pattern>> = None;
                let n = elems.len();
                for (i, el) in elems.into_iter().enumerate() {
                    match el {
                        None => out.push(None),
                        // A trailing comma after a rest element: no
                        // AssignmentRestElement admits one — pinned SyntaxError.
                        Some(Expr::SpreadTrailingComma) => {
                            return Err(early_syntax("rest element with a trailing comma"));
                        }
                        Some(Expr::Spread(inner)) => {
                            if i + 1 != n {
                                return Err(early_syntax("rest element must be last"));
                            }
                            rest = Some(Box::new(self.expr_to_pattern(*inner)?));
                        }
                        Some(Expr::Assign {
                            op: None,
                            target,
                            value,
                        }) => {
                            let pat = self.expr_to_pattern(*target)?;
                            out.push(Some(PatElem {
                                pat,
                                default: Some(Rc::new(*value)),
                            }));
                        }
                        Some(other) => {
                            let pat = self.expr_to_pattern(other)?;
                            out.push(Some(PatElem { pat, default: None }));
                        }
                    }
                }
                Ok(Pattern::Array { elems: out, rest })
            }
            Expr::Object(props) => {
                let mut out: Vec<(ObjKey, PatElem)> = Vec::new();
                let mut rest: Option<Box<Pattern>> = None;
                // Undo this literal's __proto__ accounting: in a PATTERN the
                // colon form is an ordinary property (duplicates legal).
                let protos = props
                    .iter()
                    .filter(|d| matches!(d, PropDef::ProtoData(_)))
                    .count();
                if protos == 1 {
                    self.proto_single_count -= 1;
                } else if protos >= 2 {
                    self.proto_dup_count -= 1;
                }
                let n = props.len();
                for (i, def) in props.into_iter().enumerate() {
                    match def {
                        PropDef::ProtoData(v) => {
                            let elem = match v {
                                Expr::Assign {
                                    op: None,
                                    target,
                                    value,
                                } if matches!(*target, Expr::Ident(_)) => {
                                    let pat = self.expr_to_pattern(*target)?;
                                    PatElem {
                                        pat,
                                        default: Some(Rc::new(*value)),
                                    }
                                }
                                other => {
                                    let pat = self.expr_to_pattern(other)?;
                                    PatElem { pat, default: None }
                                }
                            };
                            out.push((ObjKey::Fixed(units_from_str("__proto__")), elem));
                        }
                        PropDef::Data(_, Expr::Spread(inner)) => {
                            self.obj_spread_count -= 1;
                            if i + 1 != n {
                                return Err(early_syntax("object rest must be last"));
                            }
                            let p = self.expr_to_pattern(*inner)?;
                            if !matches!(p, Pattern::Ident(_) | Pattern::Target(_)) {
                                return Err(early_syntax("object rest target must be simple"));
                            }
                            rest = Some(Box::new(p));
                        }
                        PropDef::Data(key, v) => {
                            // A CoverInitializedName arrives as
                            // `Assign { Ident, default }` (counter-tracked).
                            let elem = match v {
                                Expr::Assign {
                                    op: None,
                                    target,
                                    value,
                                } if matches!(*target, Expr::Ident(_)) => {
                                    // Distinguish cover-init (shorthand) from
                                    // an ordinary `k: a = b` — both are legal
                                    // patterns with the same semantics; only
                                    // the counter differs. Decrement when
                                    // this was a recorded cover-init.
                                    if self.cover_init_count > 0 {
                                        self.cover_init_count -= 1;
                                    }
                                    let pat = self.expr_to_pattern(*target)?;
                                    PatElem {
                                        pat,
                                        default: Some(Rc::new(*value)),
                                    }
                                }
                                other => {
                                    let pat = self.expr_to_pattern(other)?;
                                    PatElem { pat, default: None }
                                }
                            };
                            out.push((key, elem));
                        }
                        PropDef::Method(..) | PropDef::Getter(..) | PropDef::Setter(..) => {
                            return Err(early_syntax("method in a destructuring pattern"));
                        }
                    }
                }
                Ok(Pattern::Object { props: out, rest })
            }
            Expr::Paren(inner) => match *inner {
                Expr::Ident(_) | Expr::Member { .. } | Expr::SuperMember { .. } => {
                    Ok(Pattern::Target(Rc::new(*inner)))
                }
                _ => Err(early_syntax(
                    "parenthesized literal in a destructuring pattern",
                )),
            },
            Expr::PatternAssign { .. } => {
                Err("nested pattern-assign in pattern (out of slice)".into())
            }
            _ => Err("invalid destructuring assignment target".into()),
        }
    }

    fn expect_semi(&mut self) -> R<()> {
        if self.eat(";") {
            return Ok(());
        }
        if self.at("}") || matches!(self.cur_tok(), Tok::Eof) || self.cur().newline_before {
            return Ok(()); // ASI
        }
        Err(format!(
            "expected `;`, found {:?} (no ASI opportunity)",
            self.cur_tok()
        ))
    }

    // -- expressions --------------------------------------------------------

    fn parse_expression(&mut self) -> R<Expr> {
        let e = self.parse_assignment()?;
        if !self.at(",") {
            return Ok(e);
        }
        // The comma operator: a sequence, valued at its last expression.
        let mut exprs = vec![e];
        while self.eat(",") {
            exprs.push(self.parse_assignment()?);
        }
        Ok(Expr::Seq(exprs))
    }

    /// Parse with the [+In] parameter restored (parenthesized/bracketed
    /// contexts re-allow the `in` operator).
    fn parse_assignment_in(&mut self) -> R<Expr> {
        let saved = self.no_in;
        self.no_in = false;
        let r = self.parse_assignment();
        self.no_in = saved;
        r
    }

    fn parse_expression_in(&mut self) -> R<Expr> {
        let saved = self.no_in;
        self.no_in = false;
        let r = self.parse_expression();
        self.no_in = saved;
        r
    }

    fn parse_assignment(&mut self) -> R<Expr> {
        self.enter()?;
        let r = self.parse_assignment_inner();
        self.leave();
        r
    }

    fn parse_assignment_inner(&mut self) -> R<Expr> {
        // YieldExpression is at the AssignmentExpression level and only inside
        // a generator body (an unescaped `yield`; an escaped `yield` is
        // an identifier reference, a Syntax Error we leave to the ident path).
        if self.in_generator && matches!(self.cur_tok(), Tok::Ident(id) if id == "yield") {
            return self.parse_yield();
        }
        let left = self.parse_conditional()?;
        let op = match self.cur_tok() {
            Tok::Punct("=") => None,
            Tok::Punct("+=") => Some(BinOp::Add),
            Tok::Punct("-=") => Some(BinOp::Sub),
            Tok::Punct("*=") => Some(BinOp::Mul),
            Tok::Punct("/=") => Some(BinOp::Div),
            Tok::Punct("%=") => Some(BinOp::Rem),
            Tok::Punct("**=") => Some(BinOp::Exp),
            Tok::Punct("&=") => Some(BinOp::BitAnd),
            Tok::Punct("|=") => Some(BinOp::BitOr),
            Tok::Punct("^=") => Some(BinOp::BitXor),
            Tok::Punct("<<=") => Some(BinOp::Shl),
            Tok::Punct(">>=") => Some(BinOp::Shr),
            Tok::Punct(">>>=") => Some(BinOp::Ushr),
            _ => return Ok(left),
        };
        self.pos += 1;
        if let Expr::Paren(inner) = left {
            return match *inner {
                Expr::Ident(id) => {
                    // Legal simple target; IsIdentifierRef is FALSE, so no
                    // NamedEvaluation — and the strict eval/arguments early
                    // error still applies through the parens.
                    if self.strict && (id == "eval" || id == "arguments") {
                        return Err(early_syntax(&format!(
                            "assignment to `{id}` in strict code"
                        )));
                    }
                    let value = self.parse_assignment()?;
                    Ok(Expr::Assign {
                        op,
                        target: Box::new(Expr::Ident(id)),
                        value: Box::new(value),
                    })
                }
                // `({}) = 1` / `([]) = 1`: pinned SyntaxError.
                _ => Err(early_syntax("parenthesized literal as an assignment target")),
            };
        }
        if matches!(left, Expr::Object(_) | Expr::Array(_)) {
            if op.is_some() {
                return Err("compound assignment to a pattern (out of slice)".into());
            }
            let pat = self.expr_to_pattern(left)?;
            let value = self.parse_assignment()?;
            return Ok(Expr::PatternAssign {
                pat: Rc::new(pat),
                value: Box::new(value),
            });
        }
        if !matches!(
            left,
            Expr::Ident(_) | Expr::Member { .. } | Expr::SuperMember { .. }
        ) {
            return Err("invalid assignment target".into());
        }
        // 13.15.1: in strict code, `eval`/`arguments` have AssignmentTargetType
        // ~invalid~ — assignment (simple or compound) is a Syntax Error.
        if let Expr::Ident(id) = &left
            && self.strict
            && (id == "eval" || id == "arguments")
        {
            return Err(early_syntax(&format!("assignment to `{id}` in strict code")));
        }
        let mut value = self.parse_assignment()?;
        if op.is_none() {
            if let Expr::Ident(id) = &left {
                infer_fn_name(&mut value, id);
            }
        }
        Ok(Expr::Assign {
            op,
            target: Box::new(left),
            value: Box::new(value),
        })
    }

    /// YieldExpression (14.4): `yield`, `yield [no LTH] AssignmentExpression`,
    /// or `yield [no LTH] * AssignmentExpression`. The optional-operand
    /// decision follows the grammar: a line terminator or an expression
    /// terminator after `yield` means the bare form.
    fn parse_yield(&mut self) -> R<Expr> {
        self.pos += 1; // consume `yield`
        let delegate = !self.cur().newline_before && self.eat("*");
        let arg = if delegate {
            // `yield*` requires an operand.
            Some(Box::new(self.parse_assignment()?))
        } else if self.cur().newline_before || self.yield_operand_absent() {
            None
        } else {
            Some(Box::new(self.parse_assignment()?))
        };
        Ok(Expr::Yield { delegate, arg })
    }

    /// The current token cannot begin a YieldExpression operand (so a bare
    /// `yield` ends here).
    fn yield_operand_absent(&self) -> bool {
        matches!(
            self.cur_tok(),
            Tok::Eof | Tok::Punct(")" | "]" | "}" | ";" | "," | ":")
        )
    }

    fn parse_conditional(&mut self) -> R<Expr> {
        let test = self.parse_binary(0)?;
        if !self.eat("?") {
            return Ok(test);
        }
        // ConditionalExpression[?In]: the consequent is always [+In].
        let cons = self.parse_assignment_in()?;
        self.expect(":")?;
        let alt = self.parse_assignment()?;
        Ok(Expr::Cond {
            test: Box::new(test),
            cons: Box::new(cons),
            alt: Box::new(alt),
        })
    }

    /// ExponentiationExpression (13.6): `UpdateExpression ** ExponentiationExpression`,
    /// right-associative. A UnaryExpression as the DIRECT left operand
    /// (`-2 ** 2`, `typeof x ** 2`) is an early SyntaxError.
    fn parse_exponent(&mut self) -> R<Expr> {
        // Whether the operand at THIS level begins with a unary operator is a
        // syntactic fact about the production, not the resulting AST — parens
        // (`(-1n) ** 2`, a PrimaryExpression) are erased for non-Ident/Object/
        // Array bases, so we must decide from the leading token, before parsing.
        let leading_unary = self.at_unary_prefix();
        let base = self.parse_unary()?;
        if self.at("**") {
            if leading_unary {
                return Err(early_syntax(
                    "a unary expression is not a valid left operand of `**` (parenthesize it)",
                ));
            }
            self.pos += 1;
            let exp = self.parse_exponent()?; // right-associative
            return Ok(Expr::Binary {
                op: BinOp::Exp,
                left: Box::new(base),
                right: Box::new(exp),
            });
        }
        Ok(base)
    }

    /// The current token opens a UnaryExpression prefix (`!` `-` `+` `~`
    /// `typeof` `void` `delete`, or `await` in an async body) — so the operand
    /// may not be the DIRECT left operand of `**`. `++`/`--` are
    /// UpdateExpressions and are permitted, so they are excluded here.
    fn at_unary_prefix(&self) -> bool {
        matches!(self.cur_tok(), Tok::Punct("!" | "-" | "+" | "~"))
            || self.at_kw("typeof")
            || self.at_kw("void")
            || self.at_kw("delete")
            || (self.in_async && self.at_kw("await"))
    }

    /// Precedence-climbing over the binary operators (min_prec 0 = logical-or
    /// level; higher binds tighter). `**` is handled a layer down in
    /// `parse_exponent`.
    fn parse_binary(&mut self, min_prec: u8) -> R<Expr> {
        self.enter()?;
        let r = self.parse_binary_inner(min_prec);
        self.leave();
        r
    }

    fn parse_binary_inner(&mut self, min_prec: u8) -> R<Expr> {
        // RelationalExpression : PrivateIdentifier `in` ShiftExpression (13.10)
        // — the private brand check. Legal only at relational precedence (a
        // `#x` anywhere else is a Syntax Error, judged in parse_primary).
        let mut left = if min_prec <= REL_PREC
            && !self.no_in
            && matches!(self.cur_tok(), Tok::PrivateIdent(_))
        {
            let Tok::PrivateIdent(name) = self.cur_tok().clone() else {
                unreachable!()
            };
            self.pos += 1;
            if !self.at_kw("in") {
                return Err(early_syntax(
                    "`#name` is only valid as `obj.#name` or `#name in obj`",
                ));
            }
            self.pos += 1; // `in`
            // The RHS is a ShiftExpression: an arrow function (an
            // AssignmentExpression) is a Syntax Error there, e.g.
            // `#x in () => {}`.
            if self.starts_arrow() {
                return Err(early_syntax(
                    "arrow function as the right operand of `#name in` (not a ShiftExpression)",
                ));
            }
            self.record_priv_ref(name.clone())?;
            let obj = self.parse_binary(SHIFT_PREC)?; // ShiftExpression (relational excluded)
            Expr::PrivateIn {
                name,
                obj: Box::new(obj),
            }
        } else {
            self.parse_exponent()?
        };
        loop {
            let (prec, op) = match self.cur_tok() {
                Tok::Punct("||") => (0, None),
                Tok::Punct("&&") => (1, None),
                Tok::Punct("|") => (2, Some(BinOp::BitOr)),
                Tok::Punct("^") => (3, Some(BinOp::BitXor)),
                Tok::Punct("&") => (4, Some(BinOp::BitAnd)),
                Tok::Punct("==") => (5, Some(BinOp::EqLoose)),
                Tok::Punct("!=") => (5, Some(BinOp::NeLoose)),
                Tok::Punct("===") => (5, Some(BinOp::EqStrict)),
                Tok::Punct("!==") => (5, Some(BinOp::NeStrict)),
                Tok::Punct("<") => (REL_PREC, Some(BinOp::Lt)),
                Tok::Punct("<=") => (REL_PREC, Some(BinOp::Le)),
                Tok::Punct(">") => (REL_PREC, Some(BinOp::Gt)),
                Tok::Punct(">=") => (REL_PREC, Some(BinOp::Ge)),
                Tok::Ident(id) if id == "instanceof" => (REL_PREC, Some(BinOp::InstanceOf)),
                Tok::Ident(id) if id == "in" => {
                    if self.no_in {
                        return Ok(left); // for-statement head: `in` ends here
                    }
                    (REL_PREC, Some(BinOp::In))
                }
                Tok::Punct("<<") => (SHIFT_PREC, Some(BinOp::Shl)),
                Tok::Punct(">>") => (SHIFT_PREC, Some(BinOp::Shr)),
                Tok::Punct(">>>") => (SHIFT_PREC, Some(BinOp::Ushr)),
                Tok::Punct("+") => (8, Some(BinOp::Add)),
                Tok::Punct("-") => (8, Some(BinOp::Sub)),
                Tok::Punct("*") => (9, Some(BinOp::Mul)),
                Tok::Punct("/") => (9, Some(BinOp::Div)),
                Tok::Punct("%") => (9, Some(BinOp::Rem)),
                // `??` cannot mix with `||`/`&&` and is otherwise out of slice.
                Tok::Punct("??") => {
                    return Err("nullish coalescing `??` (out of slice)".to_string())
                }
                _ => return Ok(left),
            };
            if prec < min_prec {
                return Ok(left);
            }
            self.pos += 1;
            let right = self.parse_binary(prec + 1)?;
            left = match op {
                Some(op) => Expr::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                None => Expr::Logical {
                    op: if prec == 0 { LogOp::Or } else { LogOp::And },
                    left: Box::new(left),
                    right: Box::new(right),
                },
            };
        }
    }

    fn parse_unary(&mut self) -> R<Expr> {
        self.enter()?;
        let r = self.parse_unary_inner();
        self.leave();
        r
    }

    fn parse_unary_inner(&mut self) -> R<Expr> {
        let op = match self.cur_tok() {
            Tok::Punct("!") => Some(UnOp::Not),
            Tok::Punct("-") => Some(UnOp::Neg),
            Tok::Punct("+") => Some(UnOp::Pos),
            Tok::Ident(id) if id == "typeof" => Some(UnOp::TypeOf),
            Tok::Ident(id) if id == "void" => Some(UnOp::Void),
            Tok::Ident(id) if id == "delete" => {
                self.pos += 1;
                let operand = self.parse_unary()?;
                // 13.5.1.1: strict `delete` of a (possibly parenthesized)
                // identifier reference is a Syntax Error.
                let mut peeled: &Expr = &operand;
                while let Expr::Paren(inner) = peeled {
                    peeled = inner;
                }
                if self.strict && matches!(peeled, Expr::Ident(_)) {
                    return Err(early_syntax(
                        "`delete` of an identifier reference in strict code",
                    ));
                }
                // 13.5.1.1: `delete` of a private reference is a Syntax Error.
                if matches!(
                    peeled,
                    Expr::Member {
                        prop: MemberProp::Private(_),
                        ..
                    }
                ) {
                    return Err(early_syntax("`delete` of a private reference"));
                }
                return Ok(Expr::Delete(Box::new(operand)));
            }
            Tok::Ident(id) if id == "await" => {
                if self.in_async {
                    // AwaitExpression : `await` UnaryExpression.
                    self.pos += 1;
                    let operand = self.parse_unary()?;
                    return Ok(Expr::Await(Box::new(operand)));
                }
                return Err("`await` operator outside an async function (out of slice)".to_string());
            }
            Tok::Punct("~") => Some(UnOp::BitNot),
            Tok::Punct("++" | "--") => {
                let inc = self.at("++");
                self.pos += 1;
                let target = self.parse_unary()?;
                self.check_update_target(&target)?;
                return Ok(Expr::Update {
                    inc,
                    prefix: true,
                    target: Box::new(target),
                });
            }
            _ => None,
        };
        if let Some(op) = op {
            self.pos += 1;
            let expr = self.parse_unary()?;
            return Ok(Expr::Unary {
                op,
                expr: Box::new(expr),
            });
        }
        // Postfix update (no line terminator before the operator).
        let e = self.parse_lhs()?;
        if (self.at("++") || self.at("--")) && !self.cur().newline_before {
            let inc = self.at("++");
            self.pos += 1;
            self.check_update_target(&e)?;
            return Ok(Expr::Update {
                inc,
                prefix: false,
                target: Box::new(e),
            });
        }
        Ok(e)
    }

    /// 13.4.x early errors: the update operand must be a simple assignment
    /// target; `eval`/`arguments` in strict code are Syntax Errors.
    fn check_update_target(&self, e: &Expr) -> R<()> {
        match e {
            Expr::Paren(inner) => self.check_update_target(inner),
            Expr::Ident(id) => {
                if self.strict && (id == "eval" || id == "arguments") {
                    return Err(early_syntax(&format!(
                        "`++`/`--` on `{id}` in strict code"
                    )));
                }
                Ok(())
            }
            Expr::Member { .. } | Expr::SuperMember { .. } => Ok(()),
            _ => Err("invalid ++/-- target".into()),
        }
    }

    /// A `.`-member after the dot: an ordinary `.name` or a private `.#name`
    /// (recorded for AllPrivateIdentifiersValid).
    fn member_after_dot(&mut self, obj: Expr) -> R<Expr> {
        if let Tok::PrivateIdent(name) = self.cur_tok().clone() {
            self.pos += 1;
            self.record_priv_ref(name.clone())?;
            Ok(Expr::Member {
                obj: Box::new(obj),
                prop: MemberProp::Private(name),
            })
        } else {
            let name = self.ident_name()?;
            Ok(Expr::Member {
                obj: Box::new(obj),
                prop: MemberProp::Dot(name),
            })
        }
    }

    fn parse_lhs(&mut self) -> R<Expr> {
        let mut e = self.parse_new_expr()?;
        loop {
            if self.eat(".") {
                e = self.member_after_dot(e)?;
            } else if self.eat("[") {
                let k = self.parse_expression_in()?;
                self.expect("]")?;
                e = Expr::Member {
                    obj: Box::new(e),
                    prop: MemberProp::Computed(Box::new(k)),
                };
            } else if self.at("(") {
                let args = self.parse_args()?;
                e = Expr::Call {
                    callee: Box::new(e),
                    args,
                };
            } else if self.at("?.") {
                return Err("optional chaining (out of slice)".into());
            } else if matches!(self.cur_tok(), Tok::Template(_)) {
                return Err("tagged template (out of slice)".into());
            } else {
                return Ok(e);
            }
        }
    }

    /// NewExpression / MemberExpression: member chain without calls, plus an
    /// optional argument list bound to the innermost `new`.
    fn parse_new_expr(&mut self) -> R<Expr> {
        self.enter()?;
        let r = self.parse_new_expr_inner();
        self.leave();
        r
    }

    fn parse_new_expr_inner(&mut self) -> R<Expr> {
        if self.at_kw("super") {
            self.pos += 1;
            if self.at("(") {
                if !self.in_derived_ctor {
                    // Pinned: `super(...)` outside a derived constructor.
                    return Err(early_syntax("`super` call outside a derived constructor"));
                }
                let args = self.parse_args()?;
                return Ok(Expr::SuperCall { args });
            }
            if self.eat(".") {
                self.check_super_member()?;
                let name = self.ident_name()?;
                return Ok(Expr::SuperMember {
                    prop: MemberProp::Dot(name),
                });
            }
            if self.eat("[") {
                self.check_super_member()?;
                let k = self.parse_expression_in()?;
                self.expect("]")?;
                return Ok(Expr::SuperMember {
                    prop: MemberProp::Computed(Box::new(k)),
                });
            }
            return Err("bare `super` (out of slice)".into());
        }
        if self.at_kw("new") {
            self.pos += 1;
            if self.at(".") {
                return Err("new.target (out of slice)".into());
            }
            let callee = self.parse_new_expr()?;
            let args = if self.at("(") {
                self.parse_args()?
            } else {
                Vec::new()
            };
            return Ok(Expr::New {
                callee: Box::new(callee),
                args,
            });
        }
        let mut e = self.parse_primary()?;
        loop {
            if self.eat(".") {
                e = self.member_after_dot(e)?;
            } else if self.eat("[") {
                let k = self.parse_expression_in()?;
                self.expect("]")?;
                e = Expr::Member {
                    obj: Box::new(e),
                    prop: MemberProp::Computed(Box::new(k)),
                };
            } else if matches!(self.cur_tok(), Tok::Template(_)) {
                return Err("tagged template (out of slice)".into());
            } else {
                return Ok(e);
            }
        }
    }

    fn parse_args(&mut self) -> R<Vec<Expr>> {
        self.expect("(")?;
        let mut args = Vec::new();
        if self.eat(")") {
            return Ok(args);
        }
        loop {
            if self.eat("...") {
                // A spread ArgumentList element: iterated at call time into the
                // argument list (13.3.8.1). A trailing comma after it is legal
                // (`f(...a,)`).
                let e = self.parse_assignment_in()?;
                args.push(Expr::Spread(Box::new(e)));
            } else {
                args.push(self.parse_assignment_in()?);
            }
            if self.eat(")") {
                return Ok(args);
            }
            self.expect(",")?;
            if self.eat(")") {
                return Ok(args); // trailing comma
            }
        }
    }

    /// Parse the pieces of an (untagged) template literal into an expression.
    fn parse_template(&mut self, pieces: &[TplPiece]) -> R<Expr> {
        let mut parts: Vec<TplPart> = Vec::new();
        for piece in pieces {
            match piece {
                TplPiece::Str(u) => {
                    parts.push(TplPart::Str(Rc::new(u.clone())));
                }
                TplPiece::Sub(toks) => {
                    let mut sub = Parser {
                        toks: toks.clone(),
                        pos: 0,
                        depth: self.depth,
                        strict: self.strict,
                        in_function: self.in_function,
                        breakable: 0,
                        continuable: 0,
                        no_in: false,
                        uses_arguments: false,
                        in_method: self.in_method,
                        in_derived_ctor: self.in_derived_ctor,
                        forbid_arguments: self.forbid_arguments,
                        in_generator: self.in_generator,
                        in_async: self.in_async,
                        cover_init_count: 0,
                        obj_spread_count: 0,
                        proto_single_count: 0,
                        proto_dup_count: 0,
                        saw_proto_dup: false,
                        priv_stack: Vec::new(),
                        pending_priv_refs: Vec::new(),
                        is_sub: true,
                    };
                    let e = sub.parse_expression_in()?;
                    if !matches!(sub.cur_tok(), Tok::Eof) {
                        return Err(format!(
                            "unexpected token {:?} in template substitution",
                            sub.cur_tok()
                        ));
                    }
                    // Bubble any private references the sub made (a `#x` inside
                    // a `${...}` inside a class body resolves in the enclosing
                    // class); record_priv_ref routes them to this parser's
                    // enclosing class or errors if there is none.
                    for r in std::mem::take(&mut sub.pending_priv_refs) {
                        self.record_priv_ref(r)?;
                    }
                    self.saw_proto_dup |= sub.saw_proto_dup;
                    self.uses_arguments |= sub.uses_arguments;
                    self.cover_init_count += sub.cover_init_count;
                    self.obj_spread_count += sub.obj_spread_count;
                    self.proto_single_count += sub.proto_single_count;
                    self.proto_dup_count += sub.proto_dup_count;
                    parts.push(TplPart::Expr(Box::new(e)));
                }
            }
        }
        Ok(Expr::Template(parts))
    }

    #[allow(clippy::too_many_lines)]
    fn parse_primary(&mut self) -> R<Expr> {
        match self.cur_tok().clone() {
            Tok::Num(n) => {
                self.pos += 1;
                Ok(Expr::Num(n))
            }
            Tok::BigInt(b) => {
                self.pos += 1;
                Ok(Expr::BigInt(b))
            }
            Tok::Str(u, _) => {
                self.pos += 1;
                Ok(Expr::Str(Rc::new(u)))
            }
            Tok::Template(pieces) => {
                self.pos += 1;
                self.parse_template(&pieces)
            }
            Tok::Regex(body, flags) => {
                self.pos += 1;
                // Static Semantics: an invalid RegularExpressionLiteral is an
                // early SyntaxError (12.9.5). Pattern/flag validity is judged by
                // the frozen trust-js-regexp compiler: a real SyntaxError maps to
                // the early-error trace, an unsupported (Annex-B / resource)
                // construct maps to NoCoverage (never a guessed SyntaxError).
                let flags_str: String = flags.iter().map(|&u| u as u8 as char).collect();
                match trust_js_regexp::compile(&body, &flags_str) {
                    Ok(_) => Ok(Expr::Regex {
                        body: Rc::new(body),
                        flags: Rc::new(flags),
                    }),
                    Err(trust_js_regexp::CompileError::Syntax(_)) => {
                        Err(early_syntax("invalid regular expression literal"))
                    }
                    Err(trust_js_regexp::CompileError::Unsupported(m)) => {
                        Err(format!("regex literal (unsupported construct): {m}"))
                    }
                }
            }
            Tok::Punct("(") => {
                if self.paren_starts_arrow() {
                    return self.parse_arrow_function(None, false);
                }
                self.pos += 1;
                if self.at(")") {
                    return Err("`()` without `=>` ".into());
                }
                let saved = self.no_in;
                self.no_in = false;
                let e = self.parse_expression();
                self.no_in = saved;
                let e = e?;
                self.expect(")")?;
                if self.at("=>") {
                    // The CPEAAPL reparse for forms the lookahead did not
                    // catch (newline before `=>` is a pinned SyntaxError
                    // anyway — refuse).
                    return Err("arrow with line terminator before `=>` (out of slice)".into());
                }
                // Grouping strips pattern-conversion eligibility for
                // literals (AssignmentTargetType of a ParenthesizedExpression
                // literal is ~invalid~) and IsIdentifierRef for identifiers
                // (no NamedEvaluation through parens).
                if matches!(e, Expr::Object(_) | Expr::Array(_) | Expr::Ident(_)) {
                    return Ok(Expr::Paren(Box::new(e)));
                }
                Ok(e)
            }
            Tok::Punct("[") => {
                self.pos += 1;
                let mut elems: Vec<Option<Expr>> = Vec::new();
                loop {
                    if self.eat("]") {
                        return Ok(Expr::Array(elems));
                    }
                    if self.at(",") {
                        self.pos += 1;
                        elems.push(None); // elision
                        continue;
                    }
                    if self.eat("...") {
                        // A SpreadElement: iterated at evaluation via the
                        // general iterator protocol. It also covers the
                        // AssignmentRestElement of an array assignment pattern
                        // (the CPEAAPL reparse converts it to a rest target).
                        let e = self.parse_assignment_in()?;
                        elems.push(Some(Expr::Spread(Box::new(e))));
                        if self.eat("]") {
                            return Ok(Expr::Array(elems));
                        }
                        self.expect(",")?;
                        if self.eat("]") {
                            // A trailing comma after the spread: the LITERAL is
                            // exactly `[...e]` (no extra element), but a pattern
                            // reparse must reject (a rest element admits no
                            // trailing comma). The marker records this without
                            // adding a hole (distinguishing `[...e,]` from the
                            // elision `[...e,,]`, which pushes a real hole).
                            elems.push(Some(Expr::SpreadTrailingComma));
                            return Ok(Expr::Array(elems));
                        }
                        continue;
                    }
                    elems.push(Some(self.parse_assignment_in()?));
                    if self.eat("]") {
                        return Ok(Expr::Array(elems));
                    }
                    self.expect(",")?;
                    if self.eat("]") {
                        return Ok(Expr::Array(elems)); // trailing comma
                    }
                }
            }
            Tok::Punct("{") => {
                self.pos += 1;
                self.parse_object_literal()
            }
            Tok::Ident(id) => match id.as_str() {
                "true" => {
                    self.pos += 1;
                    Ok(Expr::Bool(true))
                }
                "false" => {
                    self.pos += 1;
                    Ok(Expr::Bool(false))
                }
                "null" => {
                    self.pos += 1;
                    Ok(Expr::Null)
                }
                "this" => {
                    self.pos += 1;
                    Ok(Expr::This)
                }
                "function" => {
                    self.pos += 1;
                    Ok(Expr::Function(self.parse_function(false, false)?))
                }
                "async" if self.async_heads_function() => {
                    self.pos += 1; // `async`
                    self.pos += 1; // `function`
                    Ok(Expr::Function(self.parse_function(false, true)?))
                }
                "async" if self.async_heads_arrow() => {
                    self.pos += 1; // `async`
                    self.parse_async_arrow()
                }
                "class" => {
                    self.pos += 1;
                    let (_, class) = self.parse_class(false)?;
                    Ok(Expr::Class(class))
                }
                "super" => Err("`super` outside a method (out of slice)".to_string()),
                // Inside a function, `arguments` denotes the arguments exotic
                // object (created at call time when the body mentions it).
                // At script top level it is an ordinary identifier.
                "arguments" if self.forbid_arguments => {
                    Err(early_syntax("`arguments` in a class field initializer"))
                }
                "arguments" if self.in_function => {
                    self.pos += 1;
                    self.uses_arguments = true;
                    if self.at("=>") && !self.cur().newline_before {
                        return self.parse_arrow_function(Some("arguments".to_string()), false);
                    }
                    Ok(Expr::Ident("arguments".to_string()))
                }
                // `yield` reaching here (an operand position) is never a
                // YieldExpression — inside a generator it was intercepted at
                // the AssignmentExpression level — so it is an
                // IdentifierReference. In strict code that is a pinned early
                // Syntax Error (13.1.1); sloppy `yield` as a plain identifier
                // is legal but out of slice, so it refuses below.
                "yield" if self.strict => Err(early_syntax(
                    "`yield` as an identifier reference in strict code",
                )),
                _ if is_reserved(&id) => Err(format!("reserved word `{id}` as expression")),
                _ => {
                    self.pos += 1;
                    if self.at("=>") && !self.cur().newline_before {
                        return self.parse_arrow_function(Some(id), false);
                    }
                    Ok(Expr::Ident(id))
                }
            },
            Tok::EscIdent(id) => {
                // Escaped identifiers: judged by StringValue against the TRUE
                // ReservedWord set; NEVER act as keywords. Inside a generator
                // body `yield` is reserved regardless of strictness; inside an
                // async body `await` is reserved.
                if is_true_reserved(&id, self.strict)
                    || (self.in_generator && id == "yield")
                    || (self.in_async && id == "await")
                {
                    return Err(early_syntax(&format!(
                        "escaped reserved word `{id}` as identifier"
                    )));
                }
                if self.forbid_arguments && id == "arguments" {
                    return Err(early_syntax("`arguments` in a class field initializer"));
                }
                self.pos += 1;
                if id == "arguments" && self.in_function {
                    self.uses_arguments = true;
                }
                Ok(Expr::Ident(id))
            }
            // A bare `#name` in any operand position is a Syntax Error — a
            // PrivateIdentifier is only legal in `obj.#name` (handled by the
            // member path) or `#name in obj` (handled at relational level).
            Tok::PrivateIdent(_) => Err(early_syntax(
                "private name not in a `obj.#name` or `#name in obj` position",
            )),
            t => Err(format!("unexpected token {t:?} in expression")),
        }
    }

    /// Does the current position begin an arrow function (a `(params) =>` or
    /// a single-identifier `x =>`)? Used to reject arrows where only a
    /// higher-precedence production (e.g. a ShiftExpression) is allowed.
    fn starts_arrow(&self) -> bool {
        if self.at("(") {
            return self.paren_starts_arrow();
        }
        matches!(self.cur_tok(), Tok::Ident(id) if !is_reserved(id))
            && matches!(self.toks[self.pos + 1].tok, Tok::Punct("=>"))
            && !self.toks[self.pos + 1].newline_before
    }

    /// `async` at the current position immediately (same line) heads a
    /// `function` keyword (an async function declaration/expression).
    fn async_heads_function(&self) -> bool {
        self.at_kw("async")
            && matches!(&self.toks[self.pos + 1].tok, Tok::Ident(id) if id == "function")
            && !self.toks[self.pos + 1].newline_before
    }

    /// `async` at the current position (same line) heads an async arrow:
    /// `async Ident =>` or `async ( params ) =>`.
    fn async_heads_arrow(&self) -> bool {
        if !self.at_kw("async") {
            return false;
        }
        let n1 = &self.toks[self.pos + 1];
        if n1.newline_before {
            return false;
        }
        match &n1.tok {
            Tok::Punct("(") => self.paren_starts_arrow_at(self.pos + 1),
            Tok::Ident(id) if !is_reserved(id) => {
                matches!(&self.toks[self.pos + 2].tok, Tok::Punct("=>"))
                    && !self.toks[self.pos + 2].newline_before
            }
            _ => false,
        }
    }

    /// Token-level arrow lookahead at `(`: bracket-match to the closing `)`
    /// and check for a same-line `=>`.
    fn paren_starts_arrow(&self) -> bool {
        self.paren_starts_arrow_at(self.pos)
    }

    /// As `paren_starts_arrow`, but starting the bracket-match at token index
    /// `start` (which must be a `(`).
    fn paren_starts_arrow_at(&self, start: usize) -> bool {
        let mut depth = 0i32;
        let mut i = start;
        loop {
            match &self.toks[i].tok {
                Tok::Punct("(" | "[" | "{") => depth += 1,
                Tok::Punct(")" | "]" | "}") => {
                    depth -= 1;
                    if depth == 0 {
                        let next = &self.toks[i + 1];
                        return matches!(next.tok, Tok::Punct("=>")) && !next.newline_before;
                    }
                }
                Tok::Eof => return false,
                _ => {}
            }
            i += 1;
        }
    }

    /// An arrow function, from `(` (params) or a single-identifier param.
    /// An async arrow after the `async` keyword has been consumed: either
    /// `async Ident => body` or `async ( params ) => body`.
    fn parse_async_arrow(&mut self) -> R<Expr> {
        if self.at("(") {
            self.parse_arrow_function(None, true)
        } else {
            let id = self.binding_ident_param()?;
            self.parse_arrow_function(Some(id), true)
        }
    }

    fn parse_arrow_function(&mut self, single: Option<String>, is_async: bool) -> R<Expr> {
        let (params, rest_param, simple_params) = match single {
            Some(id) => {
                // Strict eval/arguments arrow params are early errors.
                if self.strict && (id == "eval" || id == "arguments") {
                    return Err(early_syntax(&format!(
                        "`{id}` as arrow parameter in strict code"
                    )));
                }
                (
                    vec![Param {
                        target: BindTarget::Name(id),
                        default: None,
                    }],
                    None,
                    true,
                )
            }
            None => self.parse_params()?,
        };
        if !self.eat("=>") {
            return Err("expected `=>` in arrow function".into());
        }
        // Arrow bodies: lexical this/arguments/super — keep in_method /
        // in_derived_ctor / forbid_arguments AND accumulate uses_arguments
        // into the enclosing function.
        let saved = (
            self.in_function,
            self.breakable,
            self.continuable,
            self.strict,
            self.in_generator,
            self.in_async,
        );
        self.in_function = true;
        self.breakable = 0;
        self.continuable = 0;
        // An arrow's ConciseBody does not carry [Yield]: `yield` there is not
        // a YieldExpression (arrows never suspend). An async arrow's body IS
        // [+Await].
        self.in_generator = false;
        self.in_async = is_async;
        let body: R<Vec<Stmt>> = if self.at("{") {
            self.pos += 1;
            let has_directive = self.scan_prologue_strict();
            if has_directive && !simple_params {
                (
                    self.in_function,
                    self.breakable,
                    self.continuable,
                    self.strict,
                    self.in_generator,
                    self.in_async,
                ) = saved;
                return Err(early_syntax(
                    "'use strict' directive in an arrow with a non-simple parameter list",
                ));
            }
            self.strict = self.strict || has_directive;
            self.parse_stmt_list_until_brace(true)
        } else {
            // Concise body: a single AssignmentExpression, returned.
            self.parse_assignment().map(|e| vec![Stmt::Return(Some(e))])
        };
        let strict = self.strict;
        (
            self.in_function,
            self.breakable,
            self.continuable,
            self.strict,
            self.in_generator,
            self.in_async,
        ) = saved;
        let body = body?;
        let pnames = param_names(&params, &rest_param);
        if strict {
            for p in &pnames {
                if p == "eval" || p == "arguments" {
                    return Err(early_syntax(&format!(
                        "`{p}` as strict arrow parameter"
                    )));
                }
            }
        }
        let mut vars = Vec::new();
        collect_vars(&body, &mut vars);
        let funcs = top_level_funcs(&body);
        check_scope(&body, &pnames, &vars)?;
        Ok(Expr::Arrow(Rc::new(FuncLit {
            name: None,
            inferred_name: true,
            params,
            rest_param,
            simple_params,
            body,
            strict,
            vars,
            funcs,
            // Arrows never create an arguments object (lexical resolution).
            uses_arguments: false,
            is_method: true,
            is_arrow: true,
            is_generator: false,
            is_async,
        })))
    }

    /// A property name in an object literal: identifier/string/number
    /// (fixed) or a computed `[expr]` key.
    fn parse_obj_key(&mut self) -> R<(ObjKey, Option<String>)> {
        match self.cur_tok().clone() {
            Tok::Ident(id) | Tok::EscIdent(id) => {
                self.pos += 1;
                Ok((ObjKey::Fixed(units_from_str(&id)), Some(id)))
            }
            Tok::Str(u, _) => {
                self.pos += 1;
                Ok((ObjKey::Fixed(u), None))
            }
            Tok::Num(n) => {
                self.pos += 1;
                Ok((
                    ObjKey::Fixed(units_from_str(&crate::number::js_number_to_string(n))),
                    None,
                ))
            }
            Tok::BigInt(b) => {
                self.pos += 1;
                Ok((ObjKey::Fixed(units_from_str(&b.to_str_radix(10))), None))
            }
            Tok::Punct("[") => {
                self.pos += 1;
                let e = self.parse_assignment_in()?;
                self.expect("]")?;
                Ok((ObjKey::Computed(Rc::new(e)), None))
            }
            Tok::Punct("...") => Err("object spread (out of slice)".into()),
            t => Err(format!("bad object literal key {t:?}")),
        }
    }

    fn parse_object_literal(&mut self) -> R<Expr> {
        let mut entries: Vec<PropDef> = Vec::new();
        let mut proto_data_keys = 0u32;
        if self.eat("}") {
            return Ok(Expr::Object(entries));
        }
        loop {
            if self.eat("...") {
                // Object spread: legal only when the literal reparses as a
                // pattern (object rest); counter-judged at end of parse.
                self.obj_spread_count += 1;
                let e = self.parse_assignment_in()?;
                entries.push(PropDef::Data(
                    ObjKey::Fixed(units_from_str("...")),
                    Expr::Spread(Box::new(e)),
                ));
                if self.eat("}") {
                    return Ok(self.finish_object_literal(entries, proto_data_keys));
                }
                self.expect(",")?;
                if self.eat("}") {
                    return Ok(self.finish_object_literal(entries, proto_data_keys));
                }
                continue;
            }
            // `async` heads an async method (`{ async m(){} }` /
            // `{ async *m(){} }`) when it is not itself the property name
            // (`{ async(){} }`, `{ async: 1 }`, `{ async }`, `{ async = x }`)
            // and no LineTerminator follows. `async *m(){}` is an async
            // generator method (refused in parse_method_fn).
            let is_async = self.at_kw("async")
                && !matches!(
                    self.toks[self.pos + 1].tok,
                    Tok::Punct(":" | "," | "}" | "(" | "=")
                )
                && !self.toks[self.pos + 1].newline_before;
            if is_async {
                self.pos += 1; // consume `async`
            }
            let is_gen = self.eat("*");
            // Accessor definitions: `get`/`set` followed by a property name. A
            // `*` marker forces a generator method (`*get(){}` is not one); an
            // `async` prefix forbids the accessor form.
            if let Tok::Ident(id) = self.cur_tok() {
                let is_get = id == "get";
                let is_set = id == "set";
                if !is_async
                    && !is_gen
                    && (is_get || is_set)
                    && !matches!(
                        self.toks[self.pos + 1].tok,
                        Tok::Punct(":" | "," | "}" | "(")
                    )
                {
                    self.pos += 1;
                    let (key, _) = self.parse_obj_key()?;
                    let mk = if is_get { MethodKind::Get } else { MethodKind::Set };
                    let lit = self.parse_method_fn(mk, true, false, false, false, false)?;
                    entries.push(if is_get {
                        PropDef::Getter(key, lit)
                    } else {
                        PropDef::Setter(key, lit)
                    });
                    if self.eat("}") {
                        return Ok(self.finish_object_literal(entries, proto_data_keys));
                    }
                    self.expect(",")?;
                    if self.eat("}") {
                        return Ok(self.finish_object_literal(entries, proto_data_keys));
                    }
                    continue;
                }
            }
            let (key, ident_key) = self.parse_obj_key()?;
            let def = if self.at("(") {
                // Shorthand method ([[HomeObject]] = the literal object).
                let lit =
                    self.parse_method_fn(MethodKind::Normal, true, false, false, is_gen, is_async)?;
                PropDef::Method(key, lit)
            } else if is_gen {
                // A leading `*` marks a GeneratorMethod, which REQUIRES a
                // parameter list: `({* foo})` (no `(...)`) is a pinned
                // SyntaxError — `*` is not a valid prefix of a shorthand /
                // data / cover-initialized property.
                return Err(early_syntax(
                    "`*` generator prefix without a method parameter list in object literal",
                ));
            } else if is_async {
                // An `async` prefix REQUIRES a method parameter list; there is
                // no async shorthand / data / cover-init property.
                return Err(early_syntax(
                    "`async` prefix without a method parameter list in object literal",
                ));
            } else if self.eat(":") {
                // B.3.1: `__proto__ : AssignmentExpression` (identifier or
                // string key — never computed) is the prototype-mutating
                // PropertyDefinition — but ONLY for ObjectLiteral
                // initializers, NOT for a brace form reparsed as a pattern.
                // Record the colon form; finish_object_literal counts and
                // the end-of-parse judgment (or the pattern conversion)
                // settles it.
                let is_proto = matches!(&key, ObjKey::Fixed(u)
                    if crate::value::units_eq_ascii(u, "__proto__"));
                if is_proto {
                    proto_data_keys += 1;
                }
                let mut v = self.parse_assignment_in()?;
                if let ObjKey::Fixed(u) = &key {
                    let key_s = crate::value::units_to_lossy(u);
                    infer_fn_name(&mut v, &key_s);
                }
                if is_proto {
                    PropDef::ProtoData(v)
                } else {
                    PropDef::Data(key, v)
                }
            } else if self.at(",") || self.at("}") {
                // Shorthand `{ a }` — the key must be a plain identifier.
                // (`{ __proto__ }` is an ordinary own property per spec and
                // does NOT count toward the B.3.1 duplicate rule.)
                let v = match ident_key {
                    Some(id) if id == "arguments" && self.in_function => {
                        self.uses_arguments = true;
                        Expr::Ident(id)
                    }
                    Some(id) if !is_reserved(&id) => Expr::Ident(id),
                    _ => return Err("bad shorthand property".into()),
                };
                PropDef::Data(key, v)
            } else if self.at("=") {
                // CoverInitializedName `{ a = 1 }`: only legal when this
                // literal reparses as an assignment pattern; judged at end
                // of parse via the counter.
                self.pos += 1;
                let id = match ident_key {
                    Some(id) if !is_reserved(&id) => id,
                    _ => return Err("bad cover-initialized shorthand".into()),
                };
                self.cover_init_count += 1;
                let d = self.parse_assignment_in()?;
                PropDef::Data(
                    key,
                    Expr::Assign {
                        op: None,
                        target: Box::new(Expr::Ident(id)),
                        value: Box::new(d),
                    },
                )
            } else {
                return Err(format!(
                    "expected `:` in object literal, found {:?}",
                    self.cur_tok()
                ));
            };
            entries.push(def);
            if self.eat("}") {
                return Ok(self.finish_object_literal(entries, proto_data_keys));
            }
            self.expect(",")?;
            if self.eat("}") {
                return Ok(self.finish_object_literal(entries, proto_data_keys));
            }
        }
    }

    fn finish_object_literal(&mut self, entries: Vec<PropDef>, proto_keys: u32) -> Expr {
        if proto_keys == 1 {
            self.proto_single_count += 1;
        } else if proto_keys >= 2 {
            self.proto_dup_count += 1;
        }
        Expr::Object(entries)
    }
}

/// NamedEvaluation: an anonymous function expression bound via `=` to an
/// identifier / var declarator / property key gets that name.
fn infer_fn_name(e: &mut Expr, name: &str) {
    match e {
        Expr::Function(lit) | Expr::Arrow(lit) => {
            if lit.name.is_none() {
                // FuncLit is behind Rc but uniquely owned at parse time.
                if let Some(l) = Rc::get_mut(lit) {
                    l.name = Some(name.to_string());
                    l.inferred_name = true;
                }
            }
        }
        Expr::Class(cl) => {
            // NamedEvaluation: only the `name` property — no self-binding.
            if cl.name.is_none() {
                *cl.inferred_name.borrow_mut() = Some(name.to_string());
            }
        }
        _ => {}
    }
}

/// All bound names of a parameter list (+ rest), in order.
pub(crate) fn param_names(params: &[Param], rest: &Option<BindTarget>) -> Vec<String> {
    let mut out = Vec::new();
    for p in params {
        p.target.bound_names(&mut out);
    }
    if let Some(r) = rest {
        r.bound_names(&mut out);
    }
    out
}

/// Shallow expression walker (does not enter nested function bodies).
fn walk_expr(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match e {
        Expr::Array(elems) => {
            for el in elems.iter().flatten() {
                walk_expr(el, f);
            }
        }
        Expr::Object(props) => {
            for d in props {
                match d {
                    PropDef::Data(k, v) => {
                        if let ObjKey::Computed(ke) = k {
                            walk_expr(ke, f);
                        }
                        walk_expr(v, f);
                    }
                    PropDef::ProtoData(v) => walk_expr(v, f),
                    PropDef::Method(k, _) | PropDef::Getter(k, _) | PropDef::Setter(k, _) => {
                        if let ObjKey::Computed(ke) = k {
                            walk_expr(ke, f);
                        }
                    }
                }
            }
        }
        Expr::Template(parts) => {
            for p in parts {
                if let TplPart::Expr(x) = p {
                    walk_expr(x, f);
                }
            }
        }
        Expr::Member { obj, prop } => {
            walk_expr(obj, f);
            if let MemberProp::Computed(k) = prop {
                walk_expr(k, f);
            }
        }
        Expr::SuperMember { prop } => {
            if let MemberProp::Computed(k) = prop {
                walk_expr(k, f);
            }
        }
        Expr::Call { callee, args } | Expr::New { callee, args } => {
            walk_expr(callee, f);
            for a in args {
                walk_expr(a, f);
            }
        }
        Expr::SuperCall { args } => {
            for a in args {
                walk_expr(a, f);
            }
        }
        Expr::Unary { expr, .. }
        | Expr::Delete(expr)
        | Expr::Spread(expr)
        | Expr::Paren(expr) => walk_expr(expr, f),
        Expr::Update { target, .. } => walk_expr(target, f),
        Expr::Binary { left, right, .. } | Expr::Logical { left, right, .. } => {
            walk_expr(left, f);
            walk_expr(right, f);
        }
        Expr::Cond { test, cons, alt } => {
            walk_expr(test, f);
            walk_expr(cons, f);
            walk_expr(alt, f);
        }
        Expr::Assign { target, value, .. } => {
            walk_expr(target, f);
            walk_expr(value, f);
        }
        Expr::PatternAssign { value, .. } => walk_expr(value, f),
        Expr::PrivateIn { obj, .. } => walk_expr(obj, f),
        Expr::Seq(xs) => {
            for x in xs {
                walk_expr(x, f);
            }
        }
        _ => {}
    }
}

/// var-declared names in a statement list, descending into nested statements
/// but not into nested function literals.
pub fn collect_vars(stmts: &[Stmt], out: &mut Vec<String>) {
    for s in stmts {
        collect_vars_stmt(s, out);
    }
}

fn collect_vars_stmt(s: &Stmt, out: &mut Vec<String>) {
    let push_names = |t: &BindTarget, out: &mut Vec<String>| {
        let mut ns = Vec::new();
        t.bound_names(&mut ns);
        for n in ns {
            if !out.contains(&n) {
                out.push(n);
            }
        }
    };
    match s {
        Stmt::VarDecl { kind, decls } => {
            if *kind == DeclKind::Var {
                for (t, _) in decls {
                    push_names(t, out);
                }
            }
        }
        Stmt::Block(b) => collect_vars(b, out),
        Stmt::If { cons, alt, .. } => {
            collect_vars_stmt(cons, out);
            if let Some(a) = alt {
                collect_vars_stmt(a, out);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => collect_vars_stmt(body, out),
        Stmt::For { init, body, .. } => {
            if let Some(crate::ast::ForInit::Var(decls)) = init {
                for (t, _) in decls {
                    push_names(t, out);
                }
            }
            collect_vars_stmt(body, out);
        }
        Stmt::ForIn { left, body, .. } | Stmt::ForOf { left, body, .. } => {
            if let ForInOfLeft::Var(t) = left {
                push_names(t, out);
            }
            collect_vars_stmt(body, out);
        }
        Stmt::Try {
            block,
            catch,
            finally,
        } => {
            collect_vars(block, out);
            if let Some((_, b)) = catch {
                collect_vars(b, out);
            }
            if let Some(b) = finally {
                collect_vars(b, out);
            }
        }
        Stmt::Switch { cases, .. } => {
            for (_, b) in cases {
                collect_vars(b, out);
            }
        }
        _ => {}
    }
}

fn top_level_funcs(stmts: &[Stmt]) -> Vec<Rc<FuncLit>> {
    stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::FuncDecl(f) => Some(Rc::clone(f)),
            _ => None,
        })
        .collect()
}

/// Conservative lexical-scoping check: duplicate let/const in one statement
/// list, lexical names colliding with params, and ANY overlap between the
/// scope's var set and any lexical name (over-broad: legal shadowing is
/// refused rather than risking a mis-accepted real SyntaxError).
fn check_scope(body: &[Stmt], params: &[String], vars: &[String]) -> R<()> {
    let mut lexical_all: HashSet<String> = HashSet::new();
    collect_lexical(body, &mut lexical_all)?;
    for l in &lexical_all {
        if vars.contains(l) {
            return Err(format!("var/lexical name overlap `{l}` (refused conservatively)"));
        }
        if params.contains(l) {
            return Err(format!("param/lexical name overlap `{l}`"));
        }
    }
    // Top-level function declaration names may not collide with lexical names.
    for s in body {
        if let Stmt::FuncDecl(f) = s {
            if let Some(n) = &f.name {
                if lexical_all.contains(n) {
                    return Err(format!("function/lexical name overlap `{n}`"));
                }
            }
        }
    }
    Ok(())
}

fn collect_lexical(stmts: &[Stmt], all: &mut HashSet<String>) -> R<()> {
    let mut direct: HashSet<String> = HashSet::new();
    for s in stmts {
        match s {
            Stmt::VarDecl { kind, decls } if *kind != DeclKind::Var => {
                for (t, _) in decls {
                    let mut ns = Vec::new();
                    t.bound_names(&mut ns);
                    for n in ns {
                        if !direct.insert(n.clone()) {
                            return Err(format!("duplicate lexical declaration `{n}`"));
                        }
                        all.insert(n);
                    }
                }
            }
            Stmt::ClassDecl { name, .. } => {
                if !direct.insert(name.clone()) {
                    return Err(format!("duplicate lexical declaration `{name}`"));
                }
                all.insert(name.clone());
            }
            Stmt::Block(b) => collect_lexical(b, all)?,
            Stmt::If { cons, alt, .. } => {
                collect_lexical(std::slice::from_ref(cons), all)?;
                if let Some(a) = alt {
                    collect_lexical(std::slice::from_ref(a), all)?;
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => {
                collect_lexical(std::slice::from_ref(body), all)?;
            }
            Stmt::For { body, .. }
            | Stmt::ForIn { body, .. }
            | Stmt::ForOf { body, .. } => collect_lexical(std::slice::from_ref(body), all)?,
            Stmt::Try {
                block,
                catch,
                finally,
            } => {
                collect_lexical(block, all)?;
                if let Some((_, b)) = catch {
                    collect_lexical(b, all)?;
                }
                if let Some(b) = finally {
                    collect_lexical(b, all)?;
                }
            }
            Stmt::Switch { cases, .. } => {
                let mut case_direct: HashSet<String> = HashSet::new();
                for (_, b) in cases {
                    for cs in b {
                        match cs {
                            Stmt::VarDecl { kind, decls } => {
                                if *kind != DeclKind::Var {
                                    for (t, _) in decls {
                                        let mut ns = Vec::new();
                                        t.bound_names(&mut ns);
                                        for n in ns {
                                            if !case_direct.insert(n.clone()) {
                                                return Err(format!(
                                                    "duplicate lexical declaration `{n}` in switch"
                                                ));
                                            }
                                            all.insert(n);
                                        }
                                    }
                                }
                            }
                            Stmt::ClassDecl { name, .. } => {
                                if !case_direct.insert(name.clone()) {
                                    return Err(format!(
                                        "duplicate lexical declaration `{name}` in switch"
                                    ));
                                }
                                all.insert(name.clone());
                            }
                            _ => {}
                        }
                    }
                    collect_lexical_nested_only(b, all)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn collect_lexical_nested_only(stmts: &[Stmt], all: &mut HashSet<String>) -> R<()> {
    for s in stmts {
        match s {
            Stmt::VarDecl { .. } | Stmt::ClassDecl { .. } => {}
            other => collect_lexical(std::slice::from_ref(other), all)?,
        }
    }
    Ok(())
}
