// trust-js-parse: recursive-descent parser for the ES2025 Script grammar —
// core state, scopes, labels, statements, declarations, functions, classes.
// Expressions, cover grammars, and pattern machinery live in parser_expr.rs.
//
// Early errors are enforced as each production is parsed (scope-tracked
// duplicate/lexical rules, strict-mode rules with directive-prologue
// retro-validation, label resolution, private-name resolution at class
// close). Annex B surfaces that engines accept but the S0 slice excludes are
// refused as `Unsupported`, never guessed.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::HashMap;

use crate::ast::*;
use crate::lexer::{Fail, Lexer, P, StrFlags, Token, TokenKind};
use crate::Program;

pub const ALWAYS_RESERVED: &[&str] = &[
    "break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete",
    "do", "else", "enum", "export", "extends", "false", "finally", "for", "function", "if",
    "import", "in", "instanceof", "new", "null", "return", "super", "switch", "this", "throw",
    "true", "try", "typeof", "var", "void", "while", "with",
];

pub const STRICT_RESERVED: &[&str] = &[
    "implements", "interface", "let", "package", "private", "protected", "public", "static",
    "yield",
];

const MAX_DEPTH: u32 = 220;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    /// Script top level (var boundary).
    Top,
    /// Function body incl. arrows (var boundary).
    FnBody,
    /// Class static block body (var boundary).
    StaticBlock,
    Block,
    /// Catch with a simple identifier parameter.
    CatchSimple,
    /// Catch with a destructuring parameter.
    CatchPattern,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LexKind {
    LetConst,
    Class,
    LexFn,
    CatchParam,
}

pub struct Scope {
    pub kind: ScopeKind,
    pub var_names: HashMap<String, ()>,
    pub lex: HashMap<String, LexKind>,
}

impl Scope {
    fn new(kind: ScopeKind) -> Self {
        Scope {
            kind,
            var_names: HashMap::new(),
            lex: HashMap::new(),
        }
    }
    fn is_var_boundary(&self) -> bool {
        matches!(
            self.kind,
            ScopeKind::Top | ScopeKind::FnBody | ScopeKind::StaticBlock
        )
    }
}

pub struct LabelEntry {
    pub name: String,
    pub iteration: bool,
}

/// Copy-on-save parse context flags.
#[derive(Debug, Clone, Copy)]
pub struct Ctx {
    pub strict: bool,
    /// `yield` is an expression (generator context).
    pub yield_expr: bool,
    /// `await` is an expression (async context).
    pub await_expr: bool,
    /// `return` is legal.
    pub in_function: bool,
    pub in_iteration: bool,
    pub in_switch: bool,
    pub new_target_ok: bool,
    pub super_prop_ok: bool,
    pub super_call_ok: bool,
    /// Inside a class field initializer or static block: `arguments` banned.
    pub no_arguments: bool,
    /// Inside a class static block (await banned even though await_expr).
    pub static_block: bool,
    /// Inside formal parameters: yield/await expressions banned.
    pub in_params: bool,
    /// `in` is not a relational operator here (for-statement head).
    pub no_in: bool,
    /// The next StatementListItem is directly in a case/default clause
    /// (using declarations are banned there).
    pub direct_case: bool,
    /// The current goal is Module (top-level `import`/`export`,
    /// `import.meta`, and the module lexical rules apply). Persists into
    /// nested functions (so `import.meta` stays legal), but the top-level
    /// item list is only parsed at the true module top.
    pub in_module: bool,
}

impl Ctx {
    fn top(strict: bool) -> Self {
        Ctx {
            strict,
            yield_expr: false,
            await_expr: false,
            in_function: false,
            in_iteration: false,
            in_switch: false,
            new_target_ok: false,
            super_prop_ok: false,
            super_call_ok: false,
            no_arguments: false,
            static_block: false,
            in_params: false,
            no_in: false,
            direct_case: false,
            in_module: false,
        }
    }
}

/// Pending cover-grammar errors: recorded when the construct is parsed,
/// cleared when the containing literal is reparsed/converted to a pattern,
/// raised at the nearest boundary that can no longer become a pattern.
#[derive(Debug, Clone, Copy, Default)]
pub struct Pending {
    /// `{ a = 1 }` CoverInitializedName position.
    pub cover_init: Option<usize>,
    /// duplicate non-computed `__proto__` in `key: value` form.
    pub dup_proto: Option<usize>,
}

impl Pending {
    pub fn any(&self) -> bool {
        self.cover_init.is_some() || self.dup_proto.is_some()
    }
    pub fn merge_keep_earlier(saved: Pending, cur: Pending) -> Pending {
        Pending {
            cover_init: saved.cover_init.or(cur.cover_init),
            dup_proto: saved.dup_proto.or(cur.dup_proto),
        }
    }
}

/// Declared private-name bits per class.
const PN_GET_STATIC: u8 = 1;
const PN_SET_STATIC: u8 = 2;
const PN_GET_INST: u8 = 4;
const PN_SET_INST: u8 = 8;
const PN_OTHER: u8 = 16;

pub struct ClassFrame {
    pub declared: HashMap<String, u8>,
    /// private_refs length at class-body start.
    pub refs_mark: usize,
}

pub struct Parser {
    pub lx: Lexer,
    pub tok: Token,
    pub ctx: Ctx,
    pub scopes: Vec<Scope>,
    pub labels: Vec<LabelEntry>,
    pub label_barrier: usize,
    pub class_frames: Vec<ClassFrame>,
    pub private_refs: Vec<(String, usize)>,
    pub pending: Pending,
    pub depth: u32,
}

pub type PResult<T> = Result<T, Fail>;

impl Parser {
    pub fn new(source: &str) -> Self {
        Parser {
            lx: Lexer::new(source),
            tok: Token {
                kind: TokenKind::Eof,
                start: 0,
                end: 0,
                newline_before: false,
                had_escape: false,
            },
            ctx: Ctx::top(false),
            scopes: Vec::new(),
            labels: Vec::new(),
            label_barrier: 0,
            class_frames: Vec::new(),
            private_refs: Vec::new(),
            pending: Pending::default(),
            depth: 0,
        }
    }

    pub fn parse_program(mut self, strict: bool) -> PResult<Program> {
        self.ctx = Ctx::top(strict);
        self.lx.skip_hashbang();
        self.next()?;
        self.scopes.push(Scope::new(ScopeKind::Top));
        let (body, _) = self.parse_body_statements(None, true)?;
        if !matches!(self.tok.kind, TokenKind::Eof) {
            return Err(Fail::early("unexpected token at top level"));
        }
        if let Some((name, _)) = self.private_refs.first() {
            return Err(Fail::early(format!(
                "reference to undeclared private name #{name}"
            )));
        }
        Ok(Program {
            body,
            strict: self.ctx.strict,
        })
    }

    // ---- module goal ----------------------------------------------------

    /// Parse a Module (ECMA-262 §16.2). Modules are ALWAYS strict, carry the
    /// [+Await] parameter at the top level (top-level await; `await` is a
    /// reserved word as a plain identifier), and admit `import`/`export`
    /// declarations only in the top-level ModuleItemList.
    pub fn parse_module_program(mut self) -> PResult<Program> {
        self.ctx = Ctx::top(true);
        self.ctx.in_module = true;
        // Top-level await: the module body is parsed with await as an
        // expression, which also makes bare `await` an identifier an error.
        self.ctx.await_expr = true;
        self.lx.skip_hashbang();
        self.next()?;
        self.scopes.push(Scope::new(ScopeKind::Top));
        let body = self.parse_module_item_list()?;
        if !matches!(self.tok.kind, TokenKind::Eof) {
            return Err(Fail::early("unexpected token at module top level"));
        }
        if let Some((name, _)) = self.private_refs.first() {
            return Err(Fail::early(format!(
                "reference to undeclared private name #{name}"
            )));
        }
        Ok(Program { body, strict: true })
    }

    fn parse_module_item_list(&mut self) -> PResult<Vec<Stmt>> {
        let mut stmts = Vec::new();
        // ExportedNames (external, for the duplicate-export early error) and
        // the local names referenced by a from-less `export { … }` (which must
        // be declared somewhere in the module — checked after the whole list).
        let mut exported: Vec<String> = Vec::new();
        let mut local_refs: Vec<String> = Vec::new();
        loop {
            if matches!(self.tok.kind, TokenKind::Eof) {
                break;
            }
            let s = self.parse_module_item(&mut exported, &mut local_refs)?;
            stmts.push(s);
        }
        // Every `export { x }` local reference must resolve to a top-level
        // declaration of the module (VarDeclaredNames ∪ LexicallyDeclaredNames,
        // which includes import bindings). Forward references are legal, so this
        // is checked once the full item list is known.
        let declared = self.top_declared_names();
        for r in &local_refs {
            if !declared.contains(r) {
                return Err(Fail::early(format!(
                    "export '{r}' is not declared in the module"
                )));
            }
        }
        Ok(stmts)
    }

    /// One ModuleItem: an `import`/`export` declaration, or an ordinary
    /// StatementListItem. `import` starts a declaration UNLESS it is followed by
    /// `(` (dynamic import) or `.` (`import.meta`), in which case it is an
    /// ExpressionStatement.
    fn parse_module_item(
        &mut self,
        exported: &mut Vec<String>,
        local_refs: &mut Vec<String>,
    ) -> PResult<Stmt> {
        if self.tok.is_kw("import") {
            let p = self.peek()?;
            if p.is_punct(P::LParen) || p.is_punct(P::Dot) {
                return self.parse_stmt_list_item();
            }
            return self.parse_import_declaration();
        }
        if self.tok.is_kw("export") {
            return self.parse_export_declaration(exported, local_refs);
        }
        self.parse_stmt_list_item()
    }

    /// The set of names declared at the top level of the module (Top scope var
    /// + lexical names, which includes import bindings and top-level functions).
    fn top_declared_names(&self) -> std::collections::HashSet<String> {
        let mut set = std::collections::HashSet::new();
        if let Some(scope) = self.scopes.last() {
            for k in scope.var_names.keys() {
                set.insert(k.clone());
            }
            for k in scope.lex.keys() {
                set.insert(k.clone());
            }
        }
        set
    }

    // ---- import declarations --------------------------------------------

    fn parse_import_declaration(&mut self) -> PResult<Stmt> {
        self.next()?; // import
        // `import ModuleSpecifier ;` — side-effect import.
        if matches!(self.tok.kind, TokenKind::Str { .. }) {
            let source = self.parse_module_specifier()?;
            self.check_no_import_attributes()?;
            self.semicolon()?;
            return Ok(Stmt::Import(ImportDecl {
                default: None,
                namespace: None,
                named: Vec::new(),
                source,
            }));
        }
        let mut default = None;
        let mut namespace = None;
        let mut named = Vec::new();
        if matches!(self.tok.kind, TokenKind::Ident(_)) {
            // ImportedDefaultBinding, optionally followed by NameSpaceImport
            // or NamedImports.
            default = Some(self.parse_imported_binding()?);
            if self.eat_punct(P::Comma)? {
                if self.tok.is_punct(P::Star) {
                    namespace = Some(self.parse_namespace_import()?);
                } else if self.tok.is_punct(P::LBrace) {
                    named = self.parse_named_imports()?;
                } else {
                    return Err(Fail::early(
                        "expected '*' or '{' after ',' in import clause",
                    ));
                }
            }
        } else if self.tok.is_punct(P::Star) {
            namespace = Some(self.parse_namespace_import()?);
        } else if self.tok.is_punct(P::LBrace) {
            named = self.parse_named_imports()?;
        } else {
            return Err(Fail::early("unexpected token in import declaration"));
        }
        self.expect_from()?;
        let source = self.parse_module_specifier()?;
        self.check_no_import_attributes()?;
        self.semicolon()?;
        Ok(Stmt::Import(ImportDecl {
            default,
            namespace,
            named,
            source,
        }))
    }

    /// An ImportedBinding (`BindingIdentifier[~Yield, ~Await]`), declared as a
    /// module-top lexical binding. Returns the bound name.
    fn parse_imported_binding(&mut self) -> PResult<String> {
        let name = match &self.tok.kind {
            TokenKind::Ident(n) => n.clone(),
            _ => return Err(Fail::early("expected an imported binding identifier")),
        };
        self.check_binding_ident(&name)?;
        self.declare_lexical(&name, LexKind::LetConst)?;
        self.next()?;
        Ok(name)
    }

    fn parse_namespace_import(&mut self) -> PResult<String> {
        self.next()?; // *
        if !self.tok.is_kw("as") {
            return Err(Fail::early("expected 'as' after '*' in namespace import"));
        }
        self.next()?; // as
        self.parse_imported_binding()
    }

    fn parse_named_imports(&mut self) -> PResult<Vec<ImportEntry>> {
        self.next()?; // {
        let mut out = Vec::new();
        while !self.tok.is_punct(P::RBrace) {
            let imported = self.parse_module_export_name()?;
            let local = if self.tok.is_kw("as") {
                self.next()?;
                self.parse_imported_binding()?
            } else {
                // No `as`: the ImportSpecifier is a bare ImportedBinding, so the
                // ModuleExportName must be a plain IdentifierName that is a legal
                // BindingIdentifier (a StringLiteral here is a SyntaxError).
                match &imported {
                    ModuleExportName::Ident(n) => {
                        let n = n.clone();
                        self.check_binding_ident(&n)?;
                        self.declare_lexical(&n, LexKind::LetConst)?;
                        n
                    }
                    ModuleExportName::Str(_) => {
                        return Err(Fail::early(
                            "a string import name requires an 'as' binding",
                        ));
                    }
                }
            };
            out.push(ImportEntry { imported, local });
            if !self.eat_punct(P::Comma)? {
                break;
            }
        }
        self.expect_punct(P::RBrace, "'}' in named imports")?;
        Ok(out)
    }

    // ---- export declarations --------------------------------------------

    fn parse_export_declaration(
        &mut self,
        exported: &mut Vec<String>,
        local_refs: &mut Vec<String>,
    ) -> PResult<Stmt> {
        self.next()?; // export
        // export * FromClause ; | export * as ModuleExportName FromClause ;
        if self.tok.is_punct(P::Star) {
            self.next()?;
            let alias = if self.tok.is_kw("as") {
                self.next()?;
                let name = self.parse_module_export_name()?;
                self.record_export_name(&name, exported)?;
                Some(name)
            } else {
                None
            };
            self.expect_from()?;
            let source = self.parse_module_specifier()?;
            self.check_no_import_attributes()?;
            self.semicolon()?;
            return Ok(Stmt::Export(ExportDecl::Star { alias, source }));
        }
        // export NamedExports FromClause? ;
        if self.tok.is_punct(P::LBrace) {
            let specs = self.parse_export_specifiers()?;
            let source = if self.tok.is_kw("from") {
                self.next()?;
                let s = self.parse_module_specifier()?;
                self.check_no_import_attributes()?;
                Some(s)
            } else {
                None
            };
            for sp in &specs {
                self.record_export_name(&sp.exported, exported)?;
            }
            if source.is_none() {
                // Without a FromClause the left side references a local binding:
                // it must be an identifier (a StringLiteral is a SyntaxError) and
                // must be declared in the module (checked after the whole list).
                for sp in &specs {
                    match &sp.local {
                        ModuleExportName::Ident(n) => local_refs.push(n.clone()),
                        ModuleExportName::Str(_) => {
                            return Err(Fail::early(
                                "a local export name cannot be a string literal without a module source",
                            ));
                        }
                    }
                }
            }
            self.semicolon()?;
            return Ok(Stmt::Export(ExportDecl::Named { specs, source }));
        }
        // export default …
        if self.tok.is_kw("default") {
            self.next()?;
            self.record_export_name_str("default", exported)?;
            return self.parse_export_default();
        }
        // export VariableStatement | Declaration
        let stmt = self.parse_export_declaration_stmt()?;
        for n in Self::bound_names_of_stmt(&stmt) {
            self.record_export_name_str(&n, exported)?;
        }
        Ok(Stmt::Export(ExportDecl::Decl(Box::new(stmt))))
    }

    fn parse_export_specifiers(&mut self) -> PResult<Vec<ExportEntry>> {
        self.next()?; // {
        let mut out = Vec::new();
        while !self.tok.is_punct(P::RBrace) {
            let local = self.parse_module_export_name()?;
            let exported = if self.tok.is_kw("as") {
                self.next()?;
                self.parse_module_export_name()?
            } else {
                local.clone()
            };
            out.push(ExportEntry { local, exported });
            if !self.eat_punct(P::Comma)? {
                break;
            }
        }
        self.expect_punct(P::RBrace, "'}' in export list")?;
        Ok(out)
    }

    /// `export <VariableStatement | Declaration>` — the wrapped declaration.
    fn parse_export_declaration_stmt(&mut self) -> PResult<Stmt> {
        if self.tok.is_kw("var") {
            return self.parse_var_statement(DeclKind::Var);
        }
        if self.tok.is_kw("const") {
            return self.parse_var_statement(DeclKind::Const);
        }
        if self.tok.is_kw("let") {
            return self.parse_var_statement(DeclKind::Let);
        }
        if self.tok.is_kw("function") {
            return self.parse_function_declaration(false);
        }
        if self.tok.is_kw("async") {
            let p = self.peek()?;
            if p.is_kw("function") && !p.newline_before {
                return self.parse_function_declaration(true);
            }
            return Err(Fail::early("expected 'function' after 'export async'"));
        }
        if self.tok.is_kw("class") {
            return self.parse_class_declaration();
        }
        Err(Fail::early("unexpected token after 'export'"))
    }

    /// `export default HoistableDeclaration | ClassDeclaration |
    /// AssignmentExpression ;`. The hoistable/class forms may be anonymous.
    fn parse_export_default(&mut self) -> PResult<Stmt> {
        let async_fn = self.tok.is_kw("async")
            && self.peek()?.is_kw("function")
            && !self.peek()?.newline_before;
        if self.tok.is_kw("function") || async_fn {
            let func = self.parse_default_function()?;
            return Ok(Stmt::Export(ExportDecl::Default(Box::new(Stmt::FuncDecl(
                func,
            )))));
        }
        if self.tok.is_kw("class") {
            let class = self.parse_default_class()?;
            return Ok(Stmt::Export(ExportDecl::Default(Box::new(Stmt::ClassDecl(
                class,
            )))));
        }
        let e = self.parse_assignment(false)?;
        self.semicolon()?;
        Ok(Stmt::Export(ExportDecl::Default(Box::new(Stmt::Expr(e)))))
    }

    /// A `HoistableDeclaration` in `export default` position — like a function
    /// declaration but the name is optional (anonymous default export).
    fn parse_default_function(&mut self) -> PResult<Func> {
        let is_async = if self.tok.is_kw("async") {
            self.next()?;
            true
        } else {
            false
        };
        self.next()?; // function
        let is_gen = self.eat_punct(P::Star)?;
        let name = match &self.tok.kind {
            TokenKind::Ident(n) => {
                let n = n.clone();
                self.check_binding_ident(&n)?;
                self.next()?;
                self.declare_function_name(&n)?;
                Some(n)
            }
            _ => None,
        };
        self.parse_function_rest(name, is_async, is_gen, false)
    }

    /// A `ClassDeclaration` in `export default` position — name optional.
    fn parse_default_class(&mut self) -> PResult<Class> {
        self.next()?; // class
        let name = match &self.tok.kind {
            TokenKind::Ident(n) if !self.tok.is_kw("extends") => {
                let n = n.clone();
                // Class code (incl. the name) is strict; the module already is.
                self.check_binding_ident(&n)?;
                self.next()?;
                Some(n)
            }
            _ => None,
        };
        if let Some(n) = &name {
            let n = n.clone();
            self.declare_lexical(&n, LexKind::Class)?;
        }
        self.parse_class_tail(name)
    }

    // ---- module shared helpers ------------------------------------------

    /// A `ModuleExportName`: an IdentifierName (any, including reserved words —
    /// it is a name, not a reference) or a StringLiteral (cooked value). A
    /// string whose value is not representable (a lone surrogate) is refused
    /// rather than judged.
    fn parse_module_export_name(&mut self) -> PResult<ModuleExportName> {
        match &self.tok.kind {
            TokenKind::Ident(n) => {
                let n = n.clone();
                self.next()?;
                Ok(ModuleExportName::Ident(n))
            }
            TokenKind::Str { raw, flags } => {
                let raw = raw.clone();
                let flags = *flags;
                match cook_string(&raw, flags) {
                    Some(s) => {
                        self.next()?;
                        Ok(ModuleExportName::Str(s))
                    }
                    None => Err(Fail::unsupported(
                        "module export name string with a lone surrogate",
                    )),
                }
            }
            _ => Err(Fail::early("expected a module export name")),
        }
    }

    /// A ModuleSpecifier is always a StringLiteral; returns its cooked value.
    fn parse_module_specifier(&mut self) -> PResult<String> {
        match &self.tok.kind {
            TokenKind::Str { raw, flags } => {
                let raw = raw.clone();
                let flags = *flags;
                let cooked = cook_string(&raw, flags).unwrap_or_default();
                self.next()?;
                Ok(cooked)
            }
            _ => Err(Fail::early("expected a string module specifier")),
        }
    }

    fn expect_from(&mut self) -> PResult<()> {
        if self.tok.is_kw("from") {
            self.next()
        } else {
            Err(Fail::early("expected 'from'"))
        }
    }

    /// Import attributes (`with { … }` / legacy `assert { … }`) are a grammar
    /// surface we do not judge yet: refuse rather than guess a verdict.
    fn check_no_import_attributes(&mut self) -> PResult<()> {
        if self.tok.is_kw("with") {
            return Err(Fail::unsupported("import attributes (with clause)"));
        }
        if self.tok.is_kw("assert") && !self.tok.newline_before {
            let p = self.peek()?;
            if p.is_punct(P::LBrace) && !p.newline_before {
                return Err(Fail::unsupported(
                    "import attributes (legacy assert clause)",
                ));
            }
        }
        Ok(())
    }

    /// Record an ExportedName, failing closed on a duplicate.
    fn record_export_name(
        &self,
        name: &ModuleExportName,
        exported: &mut Vec<String>,
    ) -> PResult<()> {
        let s = match name {
            ModuleExportName::Ident(n) | ModuleExportName::Str(n) => n.clone(),
        };
        self.record_export_name_str(&s, exported)
    }

    fn record_export_name_str(&self, name: &str, exported: &mut Vec<String>) -> PResult<()> {
        if exported.iter().any(|e| e == name) {
            return Err(Fail::early(format!("duplicate export name '{name}'")));
        }
        exported.push(name.to_string());
        Ok(())
    }

    /// BoundNames of an `export <declaration>` statement, for ExportedNames.
    fn bound_names_of_stmt(s: &Stmt) -> Vec<String> {
        match s {
            Stmt::Decl { decls, .. } => {
                let mut names = Vec::new();
                for (pat, _) in decls {
                    Self::collect_pat_names(pat, &mut names);
                }
                names
            }
            Stmt::FuncDecl(f) => f.name.iter().cloned().collect(),
            Stmt::ClassDecl(c) => c.name.iter().cloned().collect(),
            _ => Vec::new(),
        }
    }

    fn collect_pat_names(pat: &Pat, out: &mut Vec<String>) {
        match pat {
            Pat::Ident(n) => out.push(n.clone()),
            Pat::Array { elems, rest } => {
                for e in elems.iter().flatten() {
                    Self::collect_pat_names(e, out);
                }
                if let Some(r) = rest {
                    Self::collect_pat_names(r, out);
                }
            }
            Pat::Object { props, rest } => {
                for p in props {
                    Self::collect_pat_names(&p.value, out);
                }
                if let Some(r) = rest {
                    Self::collect_pat_names(r, out);
                }
            }
            Pat::Default(inner, _) | Pat::Rest(inner) => Self::collect_pat_names(inner, out),
            Pat::Expr(_) => {}
        }
    }

    // ---- token plumbing -------------------------------------------------

    pub fn next(&mut self) -> PResult<()> {
        self.tok = self.lx.next_token()?;
        Ok(())
    }

    /// Peek one token past the current one (Div goal), without consuming.
    pub fn peek(&mut self) -> PResult<Token> {
        let save = self.lx.pos();
        let t = self.lx.next_token();
        self.lx.seek(save);
        t
    }

    /// Peek two tokens ahead.
    pub fn peek2(&mut self) -> PResult<Token> {
        let save = self.lx.pos();
        let r = self.lx.next_token().and_then(|_| self.lx.next_token());
        self.lx.seek(save);
        r
    }

    pub fn eat_punct(&mut self, p: P) -> PResult<bool> {
        if self.tok.is_punct(p) {
            self.next()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub fn expect_punct(&mut self, p: P, what: &str) -> PResult<()> {
        if self.tok.is_punct(p) {
            self.next()
        } else {
            Err(Fail::early(format!("expected {what}")))
        }
    }

    pub fn eat_kw(&mut self, s: &str) -> PResult<bool> {
        if self.tok.is_kw(s) {
            self.next()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Automatic Semicolon Insertion for a statement terminator.
    pub fn semicolon(&mut self) -> PResult<()> {
        if self.tok.is_punct(P::Semi) {
            return self.next();
        }
        if self.tok.is_punct(P::RBrace)
            || matches!(self.tok.kind, TokenKind::Eof)
            || self.tok.newline_before
        {
            return Ok(());
        }
        Err(Fail::early("missing semicolon"))
    }

    pub fn enter(&mut self) -> PResult<DepthGuard> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(Fail::unsupported("nesting depth exceeds parser bound"));
        }
        Ok(DepthGuard)
    }
    pub fn leave(&mut self, _g: DepthGuard) {
        self.depth -= 1;
    }

    // ---- identifier classification --------------------------------------

    pub fn is_always_reserved(name: &str) -> bool {
        ALWAYS_RESERVED.contains(&name)
    }

    /// IdentifierReference / label-name legality in the current context.
    pub fn check_ident_ref(&self, name: &str) -> PResult<()> {
        if Self::is_always_reserved(name) {
            return Err(Fail::early(format!("unexpected reserved word '{name}'")));
        }
        if self.ctx.strict && STRICT_RESERVED.contains(&name) {
            return Err(Fail::early(format!(
                "'{name}' is reserved in strict mode"
            )));
        }
        if name == "yield" && self.ctx.yield_expr {
            return Err(Fail::early("'yield' is reserved in generator context"));
        }
        if name == "await" && (self.ctx.await_expr || self.ctx.static_block) {
            return Err(Fail::early("'await' is reserved in async context"));
        }
        if name == "arguments" && self.ctx.no_arguments {
            return Err(Fail::early(
                "'arguments' is not allowed in class field initializers or static blocks",
            ));
        }
        Ok(())
    }

    /// BindingIdentifier legality (declarations, params, function/class
    /// names, catch params).
    pub fn check_binding_ident(&self, name: &str) -> PResult<()> {
        self.check_ident_ref(name)?;
        if self.ctx.strict && (name == "eval" || name == "arguments") {
            return Err(Fail::early(format!(
                "cannot bind '{name}' in strict mode"
            )));
        }
        Ok(())
    }

    /// Names that become illegal retroactively when a body turns strict.
    pub fn strict_banned_binding(name: &str) -> bool {
        name == "eval" || name == "arguments" || STRICT_RESERVED.contains(&name)
    }

    // ---- scopes ---------------------------------------------------------

    pub fn push_scope(&mut self, kind: ScopeKind) {
        self.scopes.push(Scope::new(kind));
    }

    pub fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    pub fn declare_var(&mut self, name: &str) -> PResult<()> {
        let mut i = self.scopes.len();
        loop {
            if i == 0 {
                break;
            }
            i -= 1;
            let scope = &self.scopes[i];
            if let Some(kind) = scope.lex.get(name) {
                match kind {
                    LexKind::CatchParam if scope.kind == ScopeKind::CatchSimple => {
                        // Annex B B.3.4 relaxes this for simple catch params.
                        return Err(Fail::unsupported(
                            "annexB var redeclaration of simple catch parameter",
                        ));
                    }
                    _ => {
                        return Err(Fail::early(format!(
                            "identifier '{name}' has already been declared"
                        )))
                    }
                }
            }
            let boundary = scope.is_var_boundary();
            self.scopes[i].var_names.insert(name.to_string(), ());
            if boundary {
                break;
            }
        }
        Ok(())
    }

    pub fn declare_lexical(&mut self, name: &str, kind: LexKind) -> PResult<()> {
        let strict = self.ctx.strict;
        let scope = self.scopes.last_mut().expect("scope stack");
        if let Some(prev) = scope.lex.get(name) {
            if *prev == LexKind::LexFn
                && kind == LexKind::LexFn
                && !strict
                && !scope.is_var_boundary()
            {
                // Annex B B.3.3 tolerates duplicate sloppy block-level
                // function declarations.
                return Err(Fail::unsupported(
                    "annexB duplicate block-level function declaration",
                ));
            }
            return Err(Fail::early(format!(
                "identifier '{name}' has already been declared"
            )));
        }
        if scope.var_names.contains_key(name) {
            return Err(Fail::early(format!(
                "identifier '{name}' has already been declared"
            )));
        }
        scope.lex.insert(name.to_string(), kind);
        Ok(())
    }

    /// Declare a function-declaration name: var-like at var boundaries,
    /// lexical in blocks.
    pub fn declare_function_name(&mut self, name: &str) -> PResult<()> {
        let at_boundary = self
            .scopes
            .last()
            .map(|s| s.is_var_boundary())
            .unwrap_or(true);
        // At the top level of a Module, function declarations are LEXICALLY
        // declared (`function f(){} function f(){}` is a duplicate-declaration
        // SyntaxError, unlike a Script where both are var-scoped and legal).
        let at_module_top = self.ctx.in_module
            && self.scopes.last().map(|s| s.kind) == Some(ScopeKind::Top);
        if at_boundary && !at_module_top {
            self.declare_var(name)
        } else {
            self.declare_lexical(name, LexKind::LexFn)
        }
    }

    // ---- labels ---------------------------------------------------------

    fn find_label(&self, name: &str) -> Option<&LabelEntry> {
        self.labels[self.label_barrier..]
            .iter()
            .rev()
            .find(|l| l.name == name)
    }

    // ---- statements -----------------------------------------------------

    /// StatementList with directive-prologue processing. Returns the
    /// statements and whether a Use Strict Directive turned the body strict.
    pub fn parse_body_statements(
        &mut self,
        end: Option<P>,
        params_simple: bool,
    ) -> PResult<(Vec<Stmt>, bool)> {
        let mut stmts = Vec::new();
        let mut in_prologue = true;
        let mut prologue_octal = false;
        let mut became_strict = false;
        let mut has_use_strict = false;
        loop {
            match end {
                Some(p) if self.tok.is_punct(p) => break,
                None if matches!(self.tok.kind, TokenKind::Eof) => break,
                _ => {}
            }
            if matches!(self.tok.kind, TokenKind::Eof) && end.is_some() {
                return Err(Fail::early("unexpected end of input"));
            }
            let s = self.parse_stmt_list_item()?;
            if in_prologue {
                if let Stmt::Expr(Expr::Str {
                    raw,
                    any_escape,
                    octal,
                }) = &s
                {
                    if *octal {
                        prologue_octal = true;
                    }
                    if raw == "use strict" && !any_escape {
                        has_use_strict = true;
                        if !self.ctx.strict {
                            became_strict = true;
                        }
                        self.ctx.strict = true;
                    }
                } else {
                    in_prologue = false;
                }
            }
            stmts.push(s);
        }
        if has_use_strict && !params_simple {
            return Err(Fail::early(
                "'use strict' directive in a body with non-simple parameters",
            ));
        }
        if became_strict && prologue_octal {
            return Err(Fail::early(
                "octal escape in directive prologue of strict body",
            ));
        }
        Ok((stmts, became_strict))
    }

    pub fn parse_statement_list(&mut self, end: P) -> PResult<Vec<Stmt>> {
        let mut stmts = Vec::new();
        while !self.tok.is_punct(end) {
            if matches!(self.tok.kind, TokenKind::Eof) {
                return Err(Fail::early("unexpected end of input"));
            }
            stmts.push(self.parse_stmt_list_item()?);
        }
        Ok(stmts)
    }

    /// StatementListItem: statements + declarations.
    pub fn parse_stmt_list_item(&mut self) -> PResult<Stmt> {
        let g = self.enter()?;
        let r = self.parse_stmt_list_item_inner();
        self.leave(g);
        r
    }

    fn parse_stmt_list_item_inner(&mut self) -> PResult<Stmt> {
        let direct_case = self.ctx.direct_case;
        self.ctx.direct_case = false;
        let name = match &self.tok.kind {
            TokenKind::Ident(name) if !self.tok.had_escape => Some(name.clone()),
            _ => None,
        };
        if let Some(name) = name {
            match name.as_str() {
                "using" => {
                    // Explicit-resource-management: `using [no LT] Ident`.
                    let p = self.peek()?;
                    if !p.newline_before
                        && matches!(&p.kind, TokenKind::Ident(n) if !Self::is_always_reserved(n))
                    {
                        self.check_using_position(direct_case)?;
                        return self.parse_using_statement(false);
                    }
                }
                "await" => {
                    if self.ctx.await_expr && !self.ctx.static_block {
                        let p = self.peek()?;
                        if p.is_kw("using") && !p.newline_before {
                            let p2 = self.peek2()?;
                            if !p2.newline_before
                                && matches!(&p2.kind, TokenKind::Ident(n) if !Self::is_always_reserved(n))
                            {
                                self.check_using_position(direct_case)?;
                                return self.parse_using_statement(true);
                            }
                        }
                    }
                }
                "const" => return self.parse_var_statement(DeclKind::Const),
                "let" => {
                    if self.let_starts_declaration()? {
                        return self.parse_var_statement(DeclKind::Let);
                    }
                }
                "function" => return self.parse_function_declaration(false),
                "async" => {
                    let p = self.peek()?;
                    if p.is_kw("function") && !p.newline_before {
                        return self.parse_function_declaration(true);
                    }
                }
                "class" => return self.parse_class_declaration(),
                _ => {}
            }
        }
        self.parse_statement(false)
    }

    /// After a `let` token: does a lexical declaration follow?
    fn let_starts_declaration(&mut self) -> PResult<bool> {
        let p = self.peek()?;
        Ok(match &p.kind {
            TokenKind::Punct(P::LBracket) | TokenKind::Punct(P::LBrace) => true,
            TokenKind::Ident(n) => !Self::is_always_reserved(n),
            _ => false,
        })
    }

    /// Statement (no declarations). `single` = single-statement position
    /// (if/loop bodies): labelled functions and declarations are illegal.
    pub fn parse_statement(&mut self, single: bool) -> PResult<Stmt> {
        let g = self.enter()?;
        let r = self.parse_statement_inner(single);
        self.leave(g);
        r
    }

    fn parse_statement_inner(&mut self, single: bool) -> PResult<Stmt> {
        if self.tok.is_punct(P::LBrace) {
            self.next()?;
            self.push_scope(ScopeKind::Block);
            let body = self.parse_statement_list(P::RBrace)?;
            self.pop_scope();
            self.expect_punct(P::RBrace, "'}'")?;
            return Ok(Stmt::Block(body));
        }
        if self.tok.is_punct(P::Semi) {
            self.next()?;
            return Ok(Stmt::Empty);
        }
        if let TokenKind::Ident(name) = &self.tok.kind {
            if !self.tok.had_escape {
                let name = name.clone();
                match name.as_str() {
                    "var" => return self.parse_var_statement(DeclKind::Var),
                    "if" => return self.parse_if(),
                    "do" => return self.parse_do_while(),
                    "while" => return self.parse_while(),
                    "for" => return self.parse_for(),
                    "continue" | "break" => return self.parse_break_continue(&name),
                    "return" => return self.parse_return(),
                    "with" => return self.parse_with(),
                    "switch" => return self.parse_switch(),
                    "throw" => return self.parse_throw(),
                    "try" => return self.parse_try(),
                    "debugger" => {
                        self.next()?;
                        self.semicolon()?;
                        return Ok(Stmt::Debugger);
                    }
                    "function" => {
                        // Annex B B.3.2 only relaxes if/else clauses (handled
                        // in parse_if_clause_body); every other single-
                        // statement position is an error in every grammar.
                        return Err(Fail::early(
                            "function declaration in single-statement position",
                        ));
                    }
                    "class" => {
                        return Err(Fail::early(
                            "class declaration in single-statement position",
                        ))
                    }
                    "const" => {
                        return Err(Fail::early(
                            "lexical declaration in single-statement position",
                        ))
                    }
                    "async" => {
                        let p = self.peek()?;
                        if p.is_kw("function") && !p.newline_before {
                            return Err(Fail::early(
                                "async function declaration in single-statement position",
                            ));
                        }
                    }
                    "let" => {
                        let p = self.peek()?;
                        if p.is_punct(P::LBracket) {
                            return Err(Fail::early(
                                "'let [' cannot begin an expression statement",
                            ));
                        }
                        if self.ctx.strict {
                            return Err(Fail::early("'let' is reserved in strict mode"));
                        }
                        // Otherwise sloppy `let` here is an ordinary
                        // identifier expression (ASI may split `let\n{}`).
                    }
                    _ => {}
                }
                // Labelled statement?
                if self.peek()?.is_punct(P::Colon) {
                    return self.parse_labelled(single);
                }
            } else {
                // Escaped identifier at statement start; could still label.
                if self.peek()?.is_punct(P::Colon) {
                    return self.parse_labelled(single);
                }
            }
        }
        // ExpressionStatement.
        let e = self.parse_expression_statement_expr()?;
        self.semicolon()?;
        Ok(Stmt::Expr(e))
    }

    fn parse_labelled(&mut self, single: bool) -> PResult<Stmt> {
        // Collect the chain of consecutive labels.
        let mut names = Vec::new();
        loop {
            let name = match &self.tok.kind {
                TokenKind::Ident(n) => n.clone(),
                _ => break,
            };
            let is_label = self.peek()?.is_punct(P::Colon);
            if !is_label {
                break;
            }
            self.check_ident_ref(&name)?;
            if self.find_label(&name).is_some() || names.contains(&name) {
                return Err(Fail::early(format!("label '{name}' already declared")));
            }
            self.next()?; // name
            self.next()?; // ':'
            names.push(name);
        }
        let is_iter = self.tok.is_kw("for") || self.tok.is_kw("while") || self.tok.is_kw("do");
        for n in &names {
            self.labels.push(LabelEntry {
                name: n.clone(),
                iteration: is_iter,
            });
        }
        // Labelled function declarations.
        let body = if self.tok.is_kw("function") {
            if self.ctx.strict {
                for _ in &names {
                    self.labels.pop();
                }
                return Err(Fail::early("labelled function declaration in strict mode"));
            }
            if single {
                for _ in &names {
                    self.labels.pop();
                }
                return Err(Fail::unsupported(
                    "annexB labelled function in single-statement position",
                ));
            }
            let p = self.peek()?;
            if p.is_punct(P::Star) {
                for _ in &names {
                    self.labels.pop();
                }
                return Err(Fail::early("labelled generator declaration"));
            }
            self.parse_function_declaration(false)
        } else {
            self.parse_statement(single)
        };
        for _ in &names {
            self.labels.pop();
        }
        let body = body?;
        let mut stmt = body;
        for n in names.into_iter().rev() {
            stmt = Stmt::Labeled {
                label: n,
                body: Box::new(stmt),
            };
        }
        Ok(stmt)
    }

    fn parse_if(&mut self) -> PResult<Stmt> {
        self.next()?;
        self.expect_punct(P::LParen, "'(' after if")?;
        let test = self.parse_expression()?;
        self.expect_punct(P::RParen, "')'")?;
        let cons = self.parse_if_clause_body()?;
        let alt = if self.eat_kw("else")? {
            Some(Box::new(self.parse_if_clause_body()?))
        } else {
            None
        };
        Ok(Stmt::If {
            test,
            cons: Box::new(cons),
            alt,
        })
    }

    /// If-clause bodies: Annex B B.3.2 lets sloppy code put a bare function
    /// declaration here; refuse rather than implement.
    fn parse_if_clause_body(&mut self) -> PResult<Stmt> {
        if self.tok.is_kw("function") && !self.ctx.strict {
            let p = self.peek()?;
            if !p.is_punct(P::Star) {
                return Err(Fail::unsupported(
                    "annexB function declaration as if-statement clause",
                ));
            }
        }
        self.parse_statement(true)
    }

    fn parse_iteration_body(&mut self) -> PResult<Stmt> {
        let saved = self.ctx;
        self.ctx.in_iteration = true;
        let r = self.parse_statement(true);
        self.ctx = saved;
        r
    }

    fn parse_do_while(&mut self) -> PResult<Stmt> {
        self.next()?;
        let body = self.parse_iteration_body()?;
        if !self.eat_kw("while")? {
            return Err(Fail::early("expected 'while' after do body"));
        }
        self.expect_punct(P::LParen, "'('")?;
        let test = self.parse_expression()?;
        self.expect_punct(P::RParen, "')'")?;
        // The semicolon after do..while is always insertable.
        if self.tok.is_punct(P::Semi) {
            self.next()?;
        }
        Ok(Stmt::DoWhile {
            body: Box::new(body),
            test,
        })
    }

    fn parse_while(&mut self) -> PResult<Stmt> {
        self.next()?;
        self.expect_punct(P::LParen, "'('")?;
        let test = self.parse_expression()?;
        self.expect_punct(P::RParen, "')'")?;
        let body = self.parse_iteration_body()?;
        Ok(Stmt::While {
            test,
            body: Box::new(body),
        })
    }

    fn parse_break_continue(&mut self, kw: &str) -> PResult<Stmt> {
        let is_break = kw == "break";
        self.next()?;
        let mut label = None;
        if !self.tok.newline_before {
            if let TokenKind::Ident(n) = &self.tok.kind {
                if !Self::is_always_reserved(n) {
                    let n = n.clone();
                    self.check_ident_ref(&n)?;
                    label = Some(n);
                    self.next()?;
                }
            }
        }
        match &label {
            Some(n) => match self.find_label(n) {
                None => return Err(Fail::early(format!("undefined label '{n}'"))),
                Some(entry) => {
                    if !is_break && !entry.iteration {
                        return Err(Fail::early(format!(
                            "continue label '{n}' does not denote an iteration statement"
                        )));
                    }
                }
            },
            None => {
                if is_break {
                    if !self.ctx.in_iteration && !self.ctx.in_switch {
                        return Err(Fail::early("break outside of loop or switch"));
                    }
                } else if !self.ctx.in_iteration {
                    return Err(Fail::early("continue outside of loop"));
                }
            }
        }
        self.semicolon()?;
        Ok(if is_break {
            Stmt::Break(label)
        } else {
            Stmt::Continue(label)
        })
    }

    fn parse_return(&mut self) -> PResult<Stmt> {
        if !self.ctx.in_function {
            return Err(Fail::early("return outside of function"));
        }
        self.next()?;
        let arg = if self.tok.is_punct(P::Semi)
            || self.tok.is_punct(P::RBrace)
            || matches!(self.tok.kind, TokenKind::Eof)
            || self.tok.newline_before
        {
            None
        } else {
            Some(self.parse_expression()?)
        };
        self.semicolon()?;
        Ok(Stmt::Return(arg))
    }

    fn parse_with(&mut self) -> PResult<Stmt> {
        if self.ctx.strict {
            return Err(Fail::early("'with' statement in strict mode"));
        }
        self.next()?;
        self.expect_punct(P::LParen, "'('")?;
        let obj = self.parse_expression()?;
        self.expect_punct(P::RParen, "')'")?;
        let body = self.parse_statement(true)?;
        Ok(Stmt::With {
            obj,
            body: Box::new(body),
        })
    }

    fn parse_switch(&mut self) -> PResult<Stmt> {
        self.next()?;
        self.expect_punct(P::LParen, "'('")?;
        let disc = self.parse_expression()?;
        self.expect_punct(P::RParen, "')'")?;
        self.expect_punct(P::LBrace, "'{'")?;
        self.push_scope(ScopeKind::Block);
        let saved = self.ctx;
        self.ctx.in_switch = true;
        let mut cases = Vec::new();
        let mut seen_default = false;
        let r = loop {
            if self.tok.is_punct(P::RBrace) {
                break Ok(());
            }
            let test = if self.tok.is_kw("case") {
                self.next()?;
                let t = self.parse_expression()?;
                Some(t)
            } else if self.tok.is_kw("default") {
                if seen_default {
                    break Err(Fail::early("duplicate default clause in switch"));
                }
                seen_default = true;
                self.next()?;
                None
            } else {
                break Err(Fail::early("expected 'case' or 'default' in switch body"));
            };
            if let Err(e) = self.expect_punct(P::Colon, "':'") {
                break Err(e);
            }
            let mut body = Vec::new();
            while !self.tok.is_punct(P::RBrace)
                && !self.tok.is_kw("case")
                && !self.tok.is_kw("default")
            {
                if matches!(self.tok.kind, TokenKind::Eof) {
                    break;
                }
                self.ctx.direct_case = true;
                let item = self.parse_stmt_list_item();
                self.ctx.direct_case = false;
                match item {
                    Ok(s) => body.push(s),
                    Err(e) => return Err(e),
                }
            }
            cases.push(SwitchCase { test, body });
        };
        self.ctx = saved;
        self.pop_scope();
        r?;
        self.expect_punct(P::RBrace, "'}'")?;
        Ok(Stmt::Switch { disc, cases })
    }

    fn parse_throw(&mut self) -> PResult<Stmt> {
        self.next()?;
        if self.tok.newline_before {
            return Err(Fail::early("newline not allowed after throw"));
        }
        let e = self.parse_expression()?;
        self.semicolon()?;
        Ok(Stmt::Throw(e))
    }

    fn parse_try(&mut self) -> PResult<Stmt> {
        self.next()?;
        self.expect_punct(P::LBrace, "'{' after try")?;
        self.push_scope(ScopeKind::Block);
        let block = self.parse_statement_list(P::RBrace)?;
        self.pop_scope();
        self.expect_punct(P::RBrace, "'}'")?;
        let mut catch = None;
        if self.eat_kw("catch")? {
            let mut param = None;
            let simple;
            if self.eat_punct(P::LParen)? {
                let is_ident = matches!(self.tok.kind, TokenKind::Ident(_));
                simple = is_ident;
                self.push_scope(if is_ident {
                    ScopeKind::CatchSimple
                } else {
                    ScopeKind::CatchPattern
                });
                let pat = self.parse_binding_target(BindTarget::CatchParam)?;
                if self.tok.is_punct(P::Eq) {
                    return Err(Fail::early("catch parameter cannot have an initializer"));
                }
                param = Some(pat);
                self.expect_punct(P::RParen, "')'")?;
            } else {
                simple = false;
                self.push_scope(ScopeKind::CatchPattern);
            }
            let _ = simple;
            self.expect_punct(P::LBrace, "'{' after catch")?;
            let body = self.parse_statement_list(P::RBrace)?;
            self.pop_scope();
            self.expect_punct(P::RBrace, "'}'")?;
            catch = Some((param, body));
        }
        let mut finally = None;
        if self.eat_kw("finally")? {
            self.expect_punct(P::LBrace, "'{' after finally")?;
            self.push_scope(ScopeKind::Block);
            let body = self.parse_statement_list(P::RBrace)?;
            self.pop_scope();
            self.expect_punct(P::RBrace, "'}'")?;
            finally = Some(body);
        }
        if catch.is_none() && finally.is_none() {
            return Err(Fail::early("try without catch or finally"));
        }
        Ok(Stmt::Try {
            block,
            catch,
            finally,
        })
    }

    // ---- variable / lexical declarations --------------------------------

    fn parse_var_statement(&mut self, kind: DeclKind) -> PResult<Stmt> {
        self.next()?; // var/let/const
        let decls = self.parse_decl_list(kind, false)?;
        self.semicolon()?;
        Ok(Stmt::Decl { kind, decls })
    }

    /// A using declaration must live inside a block/function-ish body (not
    /// the script top level) and never directly in a case/default clause.
    fn check_using_position(&self, direct_case: bool) -> PResult<()> {
        if direct_case {
            return Err(Fail::early(
                "using declaration directly in a case or default clause",
            ));
        }
        // A using declaration is banned at the top level of a SCRIPT, but
        // ALLOWED at the top level of a Module (ModuleItemList → StatementListItem).
        if self.scopes.last().map(|s| s.kind) == Some(ScopeKind::Top) && !self.ctx.in_module {
            return Err(Fail::early(
                "using declaration at the top level of a script",
            ));
        }
        Ok(())
    }

    /// Explicit-resource-management declaration statement. Caller verified
    /// the `using [Ident]` / `await using [Ident]` shape.
    fn parse_using_statement(&mut self, is_await: bool) -> PResult<Stmt> {
        if is_await {
            self.next()?; // await
        }
        self.next()?; // using
        let kind = if is_await {
            DeclKind::AwaitUsing
        } else {
            DeclKind::Using
        };
        let mut decls = Vec::new();
        loop {
            if !matches!(self.tok.kind, TokenKind::Ident(_)) {
                return Err(Fail::early(
                    "using declaration binding must be an identifier",
                ));
            }
            let pat = self.parse_binding_target(BindTarget::LetConst)?;
            if !self.eat_punct(P::Eq)? {
                return Err(Fail::early("using declaration requires an initializer"));
            }
            let init = self.parse_assignment(false)?;
            decls.push((pat, Some(init)));
            if !self.eat_punct(P::Comma)? {
                break;
            }
        }
        self.semicolon()?;
        Ok(Stmt::Decl { kind, decls })
    }

    /// Parse a declarator list. `in_for_head`: `in` is banned in inits.
    fn parse_decl_list(
        &mut self,
        kind: DeclKind,
        in_for_head: bool,
    ) -> PResult<Vec<(Pat, Option<Expr>)>> {
        let mut decls = Vec::new();
        loop {
            let (pat, init) = self.parse_declarator(kind, in_for_head)?;
            decls.push((pat, init));
            if !self.eat_punct(P::Comma)? {
                break;
            }
        }
        Ok(decls)
    }

    fn parse_declarator(
        &mut self,
        kind: DeclKind,
        in_for_head: bool,
    ) -> PResult<(Pat, Option<Expr>)> {
        let target = match kind {
            DeclKind::Var => BindTarget::Var,
            _ => BindTarget::LetConst,
        };
        let is_pattern = self.tok.is_punct(P::LBracket) || self.tok.is_punct(P::LBrace);
        let pat = self.parse_binding_target(target)?;
        let init = if self.tok.is_punct(P::Eq) {
            self.next()?;
            let saved_no_in = self.ctx.no_in;
            self.ctx.no_in = in_for_head;
            let e = self.parse_assignment(false);
            self.ctx.no_in = saved_no_in;
            Some(e?)
        } else {
            None
        };
        if init.is_none() {
            if is_pattern {
                return Err(Fail::early("destructuring declaration requires initializer"));
            }
            if kind == DeclKind::Const {
                return Err(Fail::early("const declaration requires initializer"));
            }
        }
        Ok((pat, init))
    }

    // ---- for statements -------------------------------------------------

    fn parse_for(&mut self) -> PResult<Stmt> {
        self.next()?; // for
        let is_await = if self.tok.is_kw("await") {
            if !self.ctx.await_expr || self.ctx.static_block || self.ctx.in_params {
                return Err(Fail::early("for-await outside async function"));
            }
            self.next()?;
            true
        } else {
            false
        };
        self.expect_punct(P::LParen, "'(' after for")?;
        self.push_scope(ScopeKind::Block);
        let r = self.parse_for_inner(is_await);
        self.pop_scope();
        r
    }

    fn parse_for_inner(&mut self, is_await: bool) -> PResult<Stmt> {
        // Empty init.
        if self.tok.is_punct(P::Semi) {
            if is_await {
                return Err(Fail::early("for-await requires for-of form"));
            }
            self.next()?;
            return self.parse_for_classic(None);
        }
        // Explicit-resource-management heads: for (using x of …),
        // for (await using x of …), for (using x = …;;).
        let using_head: Option<bool> = if self.tok.is_kw("using") {
            let p = self.peek()?;
            let ident_ok = !p.newline_before
                && matches!(&p.kind, TokenKind::Ident(n) if !Self::is_always_reserved(n));
            if ident_ok && (!p.is_kw("of") || self.peek2()?.is_punct(P::Eq)) {
                Some(false)
            } else {
                None
            }
        } else if self.tok.is_kw("await") {
            let p = self.peek()?;
            if p.is_kw("using") && !p.newline_before {
                if !self.ctx.await_expr || self.ctx.static_block || self.ctx.in_params {
                    return Err(Fail::early("await using outside async context"));
                }
                let p2 = self.peek2()?;
                if !p2.newline_before
                    && matches!(&p2.kind, TokenKind::Ident(n) if !Self::is_always_reserved(n))
                {
                    Some(true)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        };
        if let Some(await_using) = using_head {
            if await_using {
                self.next()?; // await
            }
            self.next()?; // using
            let kind = if await_using {
                DeclKind::AwaitUsing
            } else {
                DeclKind::Using
            };
            let pat = self.parse_binding_target(BindTarget::LetConst)?;
            if self.tok.is_kw("of") {
                self.next()?;
                let right = self.parse_assignment(false)?;
                self.expect_punct(P::RParen, "')'")?;
                let body = self.parse_iteration_body()?;
                return Ok(Stmt::ForOf {
                    left: ForHead::Decl(kind, pat),
                    right,
                    body: Box::new(body),
                    is_await,
                });
            }
            if self.tok.is_kw("in") {
                return Err(Fail::early(
                    "using declarations are not allowed in for-in",
                ));
            }
            if is_await || await_using {
                return Err(Fail::early("await using in for requires for-of form"));
            }
            // Classic for with using declarations.
            let mut decls = Vec::new();
            let mut cur = pat;
            loop {
                if !self.eat_punct(P::Eq)? {
                    return Err(Fail::early("using declaration requires an initializer"));
                }
                let saved_no_in = self.ctx.no_in;
                self.ctx.no_in = true;
                let init = self.parse_assignment(false);
                self.ctx.no_in = saved_no_in;
                decls.push((cur, Some(init?)));
                if !self.eat_punct(P::Comma)? {
                    break;
                }
                if !matches!(self.tok.kind, TokenKind::Ident(_)) {
                    return Err(Fail::early(
                        "using declaration binding must be an identifier",
                    ));
                }
                cur = self.parse_binding_target(BindTarget::LetConst)?;
            }
            self.expect_punct(P::Semi, "';' in for header")?;
            return self.parse_for_classic(Some(ForInit::Decl(kind, decls)));
        }
        // Declaration heads.
        let decl_kind = if self.tok.is_kw("var") {
            Some(DeclKind::Var)
        } else if self.tok.is_kw("const") {
            Some(DeclKind::Const)
        } else if self.tok.is_kw("let") && self.for_let_starts_declaration()? {
            Some(DeclKind::Let)
        } else {
            None
        };
        if let Some(kind) = decl_kind {
            self.next()?;
            let target = match kind {
                DeclKind::Var => BindTarget::Var,
                _ => BindTarget::LetConst,
            };
            let is_pattern = self.tok.is_punct(P::LBracket) || self.tok.is_punct(P::LBrace);
            let pat = self.parse_binding_target(target)?;
            // Possible init on the first declarator.
            let mut init = None;
            if self.tok.is_punct(P::Eq) {
                self.next()?;
                let saved_no_in = self.ctx.no_in;
                self.ctx.no_in = true;
                let e = self.parse_assignment(false);
                self.ctx.no_in = saved_no_in;
                init = Some(e?);
            }
            if self.tok.is_kw("in") {
                if is_await {
                    return Err(Fail::early("for-await cannot use 'in'"));
                }
                if init.is_some() {
                    if kind == DeclKind::Var && !is_pattern && !self.ctx.strict {
                        return Err(Fail::unsupported(
                            "annexB for-in var declaration with initializer",
                        ));
                    }
                    return Err(Fail::early("for-in declaration cannot have an initializer"));
                }
                self.next()?;
                let right = self.parse_expression()?;
                self.expect_punct(P::RParen, "')'")?;
                let body = self.parse_iteration_body()?;
                return Ok(Stmt::ForIn {
                    left: ForHead::Decl(kind, pat),
                    right,
                    body: Box::new(body),
                });
            }
            if self.tok.is_kw("of") {
                if init.is_some() {
                    return Err(Fail::early("for-of declaration cannot have an initializer"));
                }
                self.next()?;
                let right = self.parse_assignment(false)?;
                self.expect_punct(P::RParen, "')'")?;
                let body = self.parse_iteration_body()?;
                return Ok(Stmt::ForOf {
                    left: ForHead::Decl(kind, pat),
                    right,
                    body: Box::new(body),
                    is_await,
                });
            }
            if is_await {
                return Err(Fail::early("for-await requires for-of form"));
            }
            // Classic for with declaration list.
            if init.is_none() {
                if is_pattern {
                    return Err(Fail::early(
                        "destructuring declaration requires initializer",
                    ));
                }
                if kind == DeclKind::Const {
                    return Err(Fail::early("const declaration requires initializer"));
                }
            }
            let mut decls = vec![(pat, init)];
            while self.eat_punct(P::Comma)? {
                let saved_no_in = self.ctx.no_in;
                self.ctx.no_in = true;
                let d = self.parse_declarator(kind, true);
                self.ctx.no_in = saved_no_in;
                decls.push(d?);
            }
            self.expect_punct(P::Semi, "';' in for header")?;
            return self.parse_for_classic(Some(ForInit::Decl(kind, decls)));
        }
        // Expression head.
        let first_is_let = self.tok.is_kw("let");
        let first_is_async = self.tok.is_kw("async");
        if is_await && first_is_let {
            return Err(Fail::early("for-await head cannot begin with 'let'"));
        }
        let saved_no_in = self.ctx.no_in;
        self.ctx.no_in = true;
        let e = self.parse_for_head_expression();
        self.ctx.no_in = saved_no_in;
        let e = e?;
        if self.tok.is_kw("in") {
            if is_await {
                return Err(Fail::early("for-await cannot use 'in'"));
            }
            if Self::is_plain_call(&e) {
                return Err(Fail::unsupported(
                    "engine-divergent call-expression assignment target",
                ));
            }
            let target = self.expr_to_assign_target(e, true)?;
            self.pending = crate::parser::Pending::default();
            self.next()?;
            let right = self.parse_expression()?;
            self.expect_punct(P::RParen, "')'")?;
            let body = self.parse_iteration_body()?;
            return Ok(Stmt::ForIn {
                left: ForHead::Pat(target),
                right,
                body: Box::new(body),
            });
        }
        if self.tok.is_kw("of") {
            if first_is_let {
                return Err(Fail::early("for-of head cannot begin with 'let'"));
            }
            if !is_await && first_is_async && matches!(&e, Expr::Ident(n) if n == "async") {
                return Err(Fail::early("for-of head cannot be the identifier 'async'"));
            }
            if Self::is_plain_call(&e) {
                return Err(Fail::unsupported(
                    "engine-divergent call-expression assignment target",
                ));
            }
            let target = self.expr_to_assign_target(e, true)?;
            self.pending = crate::parser::Pending::default();
            self.next()?;
            let right = self.parse_assignment(false)?;
            self.expect_punct(P::RParen, "')'")?;
            let body = self.parse_iteration_body()?;
            return Ok(Stmt::ForOf {
                left: ForHead::Pat(target),
                right,
                body: Box::new(body),
                is_await,
            });
        }
        if is_await {
            return Err(Fail::early("for-await requires for-of form"));
        }
        if self.pending.any() {
            return Err(self.pending_error());
        }
        self.expect_punct(P::Semi, "';' in for header")?;
        self.parse_for_classic(Some(ForInit::Expr(e)))
    }

    /// After `for` in a for-head: does `let` start a ForDeclaration?
    fn for_let_starts_declaration(&mut self) -> PResult<bool> {
        if self.ctx.strict {
            return Ok(true);
        }
        let p = self.peek()?;
        Ok(match &p.kind {
            TokenKind::Punct(P::LBracket) | TokenKind::Punct(P::LBrace) => true,
            TokenKind::Ident(n) => !Self::is_always_reserved(n),
            _ => false,
        })
    }

    fn parse_for_classic(&mut self, init: Option<ForInit>) -> PResult<Stmt> {
        let test = if self.tok.is_punct(P::Semi) {
            None
        } else {
            Some(self.parse_expression()?)
        };
        self.expect_punct(P::Semi, "';' in for header")?;
        let update = if self.tok.is_punct(P::RParen) {
            None
        } else {
            Some(self.parse_expression()?)
        };
        self.expect_punct(P::RParen, "')'")?;
        let body = self.parse_iteration_body()?;
        Ok(Stmt::For {
            init,
            test,
            update,
            body: Box::new(body),
        })
    }

    // ---- functions ------------------------------------------------------

    fn parse_function_declaration(&mut self, is_async: bool) -> PResult<Stmt> {
        if is_async {
            self.next()?; // async
        }
        self.next()?; // function
        let is_gen = self.eat_punct(P::Star)?;
        // Declaration name: BindingIdentifier[?Yield, ?Await] in the OUTER
        // context; generator/async names additionally cannot be yield/await.
        let name = match &self.tok.kind {
            TokenKind::Ident(n) => {
                let n = n.clone();
                // Declaration names use the OUTER context (sloppy top-level
                // `function* yield() {}` / `async function await() {}` are
                // valid per the [?Yield, ?Await] grammar parameters).
                self.check_binding_ident(&n)?;
                self.next()?;
                n
            }
            _ => return Err(Fail::early("function declaration requires a name")),
        };
        self.declare_function_name(&name)?;
        let func = self.parse_function_rest(Some(name), is_async, is_gen, false)?;
        Ok(Stmt::FuncDecl(func))
    }

    /// Parse a function expression (after `function` has been seen; caller
    /// consumed nothing yet beyond knowing async-ness).
    pub fn parse_function_expression(&mut self, is_async: bool) -> PResult<Expr> {
        if is_async {
            self.next()?; // async
        }
        self.next()?; // function
        let is_gen = self.eat_punct(P::Star)?;
        let name = match &self.tok.kind {
            TokenKind::Ident(n) => {
                let n = n.clone();
                // FunctionExpression name is [~Yield, ~Await] of the outer
                // context, but generator/async expressions bind their name
                // in their own context.
                let saved = self.ctx;
                self.ctx.yield_expr = is_gen;
                self.ctx.await_expr = is_async;
                self.ctx.static_block = false;
                let r = self.check_binding_ident(&n);
                self.ctx = saved;
                r?;
                self.next()?;
                Some(n)
            }
            _ => None,
        };
        let func = self.parse_function_rest(name, is_async, is_gen, false)?;
        Ok(Expr::Function(func))
    }

    /// Common tail: `( params ) { body }` with context switch and strict
    /// retro-validation. `unique_params`: duplicates always error.
    pub fn parse_function_rest(
        &mut self,
        name: Option<String>,
        is_async: bool,
        is_gen: bool,
        unique_params: bool,
    ) -> PResult<Func> {
        let saved_ctx = self.ctx;
        let saved_barrier = self.label_barrier;
        self.label_barrier = self.labels.len();
        self.ctx.yield_expr = is_gen;
        self.ctx.await_expr = is_async;
        self.ctx.in_function = true;
        self.ctx.in_iteration = false;
        self.ctx.in_switch = false;
        self.ctx.new_target_ok = true;
        self.ctx.super_prop_ok = false;
        self.ctx.super_call_ok = false;
        self.ctx.no_arguments = false;
        self.ctx.static_block = false;
        self.ctx.no_in = false;

        self.push_scope(ScopeKind::FnBody);
        let r = self.parse_function_params_and_body(name, is_async, is_gen, false, unique_params);
        self.pop_scope();
        self.label_barrier = saved_barrier;
        self.ctx = saved_ctx;
        r
    }

    /// Assumes context + scope are set. Parses `( params ) { body }`.
    fn parse_function_params_and_body(
        &mut self,
        name: Option<String>,
        is_async: bool,
        is_gen: bool,
        is_arrow: bool,
        unique_params: bool,
    ) -> PResult<Func> {
        self.expect_punct(P::LParen, "'(' before parameters")?;
        let info = self.parse_formal_params(unique_params)?;
        self.expect_punct(P::LBrace, "'{' before function body")?;
        let (body, became_strict) = self.parse_body_statements(Some(P::RBrace), info.simple)?;
        self.expect_punct(P::RBrace, "'}' after function body")?;
        if became_strict {
            self.revalidate_strict_params(&info, name.as_deref())?;
        }
        Ok(Func {
            name,
            params: info.params,
            body,
            expr_body: None,
            is_async,
            is_gen,
            is_arrow,
            strict: self.ctx.strict,
        })
    }

    pub fn revalidate_strict_params(&self, info: &ParamInfo, name: Option<&str>) -> PResult<()> {
        for n in &info.names {
            if Self::strict_banned_binding(n) {
                return Err(Fail::early(format!(
                    "parameter name '{n}' is illegal in strict mode"
                )));
            }
        }
        if info.has_dup {
            return Err(Fail::early("duplicate parameter names in strict mode"));
        }
        if let Some(n) = name {
            if Self::strict_banned_binding(n) {
                return Err(Fail::early(format!(
                    "function name '{n}' is illegal in strict mode"
                )));
            }
        }
        Ok(())
    }

    // ---- classes --------------------------------------------------------

    fn parse_class_declaration(&mut self) -> PResult<Stmt> {
        self.next()?; // class
        // Class code (including the name) is strict.
        let name = match &self.tok.kind {
            TokenKind::Ident(n) => {
                let n = n.clone();
                let saved = self.ctx;
                self.ctx.strict = true;
                let r = self.check_binding_ident(&n);
                self.ctx = saved;
                r?;
                self.next()?;
                n
            }
            _ => return Err(Fail::early("class declaration requires a name")),
        };
        self.declare_lexical(&name, LexKind::Class)?;
        let class = self.parse_class_tail(Some(name))?;
        Ok(Stmt::ClassDecl(class))
    }

    pub fn parse_class_expression(&mut self) -> PResult<Expr> {
        self.next()?; // class
        let name = match &self.tok.kind {
            TokenKind::Ident(n) if !self.tok.is_kw("extends") => {
                let n = n.clone();
                let saved = self.ctx;
                self.ctx.strict = true;
                let r = self.check_binding_ident(&n);
                self.ctx = saved;
                r?;
                self.next()?;
                Some(n)
            }
            _ => None,
        };
        let class = self.parse_class_tail(name)?;
        Ok(Expr::Class(class))
    }

    fn parse_class_tail(&mut self, name: Option<String>) -> PResult<Class> {
        let saved_ctx = self.ctx;
        self.ctx.strict = true;
        let r = self.parse_class_tail_inner(name);
        self.ctx = saved_ctx;
        r
    }

    fn parse_class_tail_inner(&mut self, name: Option<String>) -> PResult<Class> {
        let heritage = if self.eat_kw("extends")? {
            Some(Box::new(self.parse_lhs_expression()?))
        } else {
            None
        };
        let derived = heritage.is_some();
        self.expect_punct(P::LBrace, "'{' before class body")?;
        self.class_frames.push(ClassFrame {
            declared: HashMap::new(),
            refs_mark: self.private_refs.len(),
        });
        let r = self.parse_class_body(derived);
        let frame = self.class_frames.pop().expect("class frame");
        // Resolve private references recorded within this class body:
        // declared here → resolved (dropped); otherwise they stay pending
        // for an enclosing class, or fail now when there is none.
        let refs = std::mem::take(&mut self.private_refs);
        let mut kept = Vec::new();
        let mut unresolved_here: Option<String> = None;
        for (i, (n, pos)) in refs.into_iter().enumerate() {
            if i < frame.refs_mark {
                kept.push((n, pos));
            } else if frame.declared.contains_key(&n) {
                // resolved
            } else {
                if unresolved_here.is_none() {
                    unresolved_here = Some(n.clone());
                }
                kept.push((n, pos));
            }
        }
        self.private_refs = kept;
        let elements = r?;
        if self.class_frames.is_empty() {
            if let Some(n) = unresolved_here {
                return Err(Fail::early(format!(
                    "reference to undeclared private name #{n}"
                )));
            }
        }
        self.expect_punct(P::RBrace, "'}' after class body")?;
        Ok(Class {
            name,
            heritage,
            elements,
        })
    }

    fn declare_private(&mut self, name: &str, bit: u8) -> PResult<()> {
        if name == "constructor" {
            return Err(Fail::early("private name #constructor is not allowed"));
        }
        let frame = self.class_frames.last_mut().expect("class frame");
        let entry = frame.declared.entry(name.to_string()).or_insert(0);
        let existing = *entry;
        let compatible = match bit {
            PN_GET_STATIC => existing == 0 || existing == PN_SET_STATIC,
            PN_SET_STATIC => existing == 0 || existing == PN_GET_STATIC,
            PN_GET_INST => existing == 0 || existing == PN_SET_INST,
            PN_SET_INST => existing == 0 || existing == PN_GET_INST,
            _ => existing == 0,
        };
        if !compatible {
            return Err(Fail::early(format!("duplicate private name #{name}")));
        }
        *entry |= bit;
        Ok(())
    }

    fn parse_class_body(&mut self, derived: bool) -> PResult<Vec<ClassElement>> {
        let mut elements = Vec::new();
        let mut seen_ctor = false;
        while !self.tok.is_punct(P::RBrace) {
            if matches!(self.tok.kind, TokenKind::Eof) {
                return Err(Fail::early("unexpected end of input in class body"));
            }
            if self.eat_punct(P::Semi)? {
                continue;
            }
            let el = self.parse_class_element(derived, &mut seen_ctor)?;
            elements.push(el);
        }
        Ok(elements)
    }

    fn parse_class_element(
        &mut self,
        derived: bool,
        seen_ctor: &mut bool,
    ) -> PResult<ClassElement> {
        // `static` modifier: `static` followed by anything that is not
        // `=`, `;`, `(`, `}` is the modifier.
        let mut is_static = false;
        if self.tok.is_kw("static") {
            let p = self.peek()?;
            let is_field_or_method_named_static = matches!(
                p.kind,
                TokenKind::Punct(P::Eq)
                    | TokenKind::Punct(P::Semi)
                    | TokenKind::Punct(P::LParen)
                    | TokenKind::Punct(P::RBrace)
            );
            if !is_field_or_method_named_static {
                is_static = true;
                self.next()?;
            }
        }
        // Static initialization block.
        if is_static && self.tok.is_punct(P::LBrace) {
            return self.parse_static_block();
        }
        // Modifier scan: async / * / get / set.
        let mut is_async = false;
        let mut is_gen = false;
        let mut accessor: Option<MethodKind> = None;
        if self.tok.is_kw("async") {
            let p = self.peek()?;
            let name_follows = !p.newline_before
                && (self.token_is_property_name_start(&p) || p.is_punct(P::Star));
            if name_follows {
                is_async = true;
                self.next()?;
            }
        }
        if self.tok.is_punct(P::Star) {
            is_gen = true;
            self.next()?;
        }
        if !is_gen && !is_async && (self.tok.is_kw("get") || self.tok.is_kw("set")) {
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
        let key = self.parse_property_name()?;
        let key_name = self.non_computed_key_string(&key);
        // Method?
        if self.tok.is_punct(P::LParen) {
            let is_ctor = !is_static
                && accessor.is_none()
                && !is_async
                && !is_gen
                && key_name.as_deref() == Some("constructor");
            if !is_ctor
                && !is_static
                && key_name.as_deref() == Some("constructor")
                && !matches!(key, PropKey::Private(_))
            {
                return Err(Fail::early(
                    "class constructor may not be an accessor, generator, or async method",
                ));
            }
            if is_static && key_name.as_deref() == Some("prototype") {
                return Err(Fail::early("static class member may not be named 'prototype'"));
            }
            if let PropKey::Private(n) = &key {
                let n = n.clone();
                let bit = match (accessor.clone(), is_static) {
                    (Some(MethodKind::Get), true) => PN_GET_STATIC,
                    (Some(MethodKind::Get), false) => PN_GET_INST,
                    (Some(MethodKind::Set), true) => PN_SET_STATIC,
                    (Some(MethodKind::Set), false) => PN_SET_INST,
                    _ => PN_OTHER,
                };
                self.declare_private(&n, bit)?;
            }
            if is_ctor {
                if *seen_ctor {
                    return Err(Fail::early("duplicate constructor in class"));
                }
                *seen_ctor = true;
            }
            let kind = if is_ctor {
                MethodKind::Constructor
            } else {
                accessor.clone().unwrap_or(MethodKind::Method)
            };
            let func = self.parse_method_function(
                is_async,
                is_gen,
                &kind,
                /*super_call_ok=*/ is_ctor && derived,
            )?;
            return Ok(ClassElement::Method {
                is_static,
                kind,
                key,
                func,
            });
        }
        // Field.
        if is_async || is_gen || accessor.is_some() {
            return Err(Fail::early("expected '(' after method name"));
        }
        if key_name.as_deref() == Some("constructor") {
            return Err(Fail::early("class field may not be named 'constructor'"));
        }
        if is_static && key_name.as_deref() == Some("prototype") {
            return Err(Fail::early("static class member may not be named 'prototype'"));
        }
        if let PropKey::Private(n) = &key {
            let n = n.clone();
            self.declare_private(&n, PN_OTHER)?;
        }
        let init = if self.eat_punct(P::Eq)? {
            let saved_ctx = self.ctx;
            let saved_barrier = self.label_barrier;
            self.label_barrier = self.labels.len();
            self.ctx.yield_expr = false;
            self.ctx.await_expr = false;
            self.ctx.in_function = false;
            self.ctx.in_iteration = false;
            self.ctx.in_switch = false;
            self.ctx.new_target_ok = true;
            self.ctx.super_prop_ok = true;
            self.ctx.super_call_ok = false;
            self.ctx.no_arguments = true;
            self.ctx.static_block = false;
            self.ctx.no_in = false;
            self.push_scope(ScopeKind::FnBody);
            let e = self.parse_assignment(false);
            self.pop_scope();
            self.label_barrier = saved_barrier;
            self.ctx = saved_ctx;
            Some(e?)
        } else {
            None
        };
        self.class_field_semicolon()?;
        Ok(ClassElement::Field {
            is_static,
            key,
            init,
        })
    }

    fn class_field_semicolon(&mut self) -> PResult<()> {
        if self.tok.is_punct(P::Semi) {
            return self.next();
        }
        if self.tok.is_punct(P::RBrace) || self.tok.newline_before {
            return Ok(());
        }
        Err(Fail::early("missing semicolon after class field"))
    }

    fn parse_static_block(&mut self) -> PResult<ClassElement> {
        self.next()?; // '{'
        let saved_ctx = self.ctx;
        let saved_barrier = self.label_barrier;
        self.label_barrier = self.labels.len();
        self.ctx.yield_expr = false;
        self.ctx.await_expr = true; // await is reserved, and its use errors
        self.ctx.in_function = false;
        self.ctx.in_iteration = false;
        self.ctx.in_switch = false;
        self.ctx.new_target_ok = true;
        self.ctx.super_prop_ok = true;
        self.ctx.super_call_ok = false;
        self.ctx.no_arguments = true;
        self.ctx.static_block = true;
        self.ctx.no_in = false;
        self.push_scope(ScopeKind::StaticBlock);
        let body = self.parse_statement_list(P::RBrace);
        self.pop_scope();
        self.label_barrier = saved_barrier;
        self.ctx = saved_ctx;
        let body = body?;
        self.expect_punct(P::RBrace, "'}' after static block")?;
        Ok(ClassElement::StaticBlock(body))
    }

    /// Method body shared by classes and object literals.
    pub fn parse_method_function(
        &mut self,
        is_async: bool,
        is_gen: bool,
        kind: &MethodKind,
        super_call_ok: bool,
    ) -> PResult<Func> {
        let saved_ctx = self.ctx;
        let saved_barrier = self.label_barrier;
        self.label_barrier = self.labels.len();
        self.ctx.yield_expr = is_gen;
        self.ctx.await_expr = is_async;
        self.ctx.in_function = true;
        self.ctx.in_iteration = false;
        self.ctx.in_switch = false;
        self.ctx.new_target_ok = true;
        self.ctx.super_prop_ok = true;
        self.ctx.super_call_ok = super_call_ok;
        self.ctx.no_arguments = false;
        self.ctx.static_block = false;
        self.ctx.no_in = false;
        self.push_scope(ScopeKind::FnBody);
        let r = self.parse_method_inner(is_async, is_gen, kind);
        self.pop_scope();
        self.label_barrier = saved_barrier;
        self.ctx = saved_ctx;
        r
    }

    fn parse_method_inner(
        &mut self,
        is_async: bool,
        is_gen: bool,
        kind: &MethodKind,
    ) -> PResult<Func> {
        self.expect_punct(P::LParen, "'(' before parameters")?;
        let info = self.parse_formal_params(true)?;
        match kind {
            MethodKind::Get => {
                if !info.params.is_empty() {
                    return Err(Fail::early("getter must have no parameters"));
                }
            }
            MethodKind::Set => {
                if info.params.len() != 1 || info.has_rest {
                    return Err(Fail::early("setter must have exactly one parameter"));
                }
            }
            _ => {}
        }
        self.expect_punct(P::LBrace, "'{' before method body")?;
        let (body, became_strict) = self.parse_body_statements(Some(P::RBrace), info.simple)?;
        self.expect_punct(P::RBrace, "'}' after method body")?;
        if became_strict {
            self.revalidate_strict_params(&info, None)?;
        }
        Ok(Func {
            name: None,
            params: info.params,
            body,
            expr_body: None,
            is_async,
            is_gen,
            is_arrow: false,
            strict: self.ctx.strict,
        })
    }

    pub fn token_is_property_name_start(&self, t: &Token) -> bool {
        matches!(
            t.kind,
            TokenKind::Ident(_)
                | TokenKind::Str { .. }
                | TokenKind::Num { .. }
                | TokenKind::PrivateIdent(_)
                | TokenKind::Punct(P::LBracket)
        )
    }

    /// The cooked string of a non-computed key, for constructor/__proto__/
    /// prototype comparisons.
    pub fn non_computed_key_string(&self, key: &PropKey) -> Option<String> {
        match key {
            PropKey::Ident(n) => Some(n.clone()),
            PropKey::Str(cooked) => Some(cooked.clone()),
            _ => None,
        }
    }
}

pub struct DepthGuard;

/// What a binding pattern binds into.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindTarget {
    Var,
    LetConst,
    Param,
    CatchParam,
}

/// Collected formal-parameter facts for retro strict validation.
pub struct ParamInfo {
    pub params: Vec<Pat>,
    pub names: Vec<String>,
    pub simple: bool,
    pub has_dup: bool,
    pub has_rest: bool,
}

/// Cook a string literal to its exact value, with true UTF-16 semantics: a
/// surrogate PAIR written as two `\uXXXX` escapes composes to the astral
/// character; a LONE surrogate has no Rust `String` representation, so the
/// cook refuses (`None`) and the caller must treat the construct as
/// Unsupported rather than silently mis-keying (the M1 D2 head found the
/// old lossy behavior; see the parse-verdict discipline).
pub fn cook_string(raw: &str, _flags: StrFlags) -> Option<String> {
    let chars: Vec<char> = raw.chars().collect();
    let mut units: Vec<u16> = Vec::with_capacity(chars.len());
    let push_scalar = |units: &mut Vec<u16>, v: u32| {
        if v <= 0xFFFF {
            units.push(v as u16);
        } else if let Some(ch) = char::from_u32(v) {
            let mut buf = [0u16; 2];
            units.extend_from_slice(ch.encode_utf16(&mut buf));
        }
    };
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c != '\\' {
            let mut buf = [0u16; 2];
            units.extend_from_slice(c.encode_utf16(&mut buf));
            i += 1;
            continue;
        }
        i += 1;
        if i >= chars.len() {
            break;
        }
        let e = chars[i];
        match e {
            'n' => {
                units.push(0x0A);
                i += 1;
            }
            't' => {
                units.push(0x09);
                i += 1;
            }
            'r' => {
                units.push(0x0D);
                i += 1;
            }
            'b' => {
                units.push(0x08);
                i += 1;
            }
            'f' => {
                units.push(0x0C);
                i += 1;
            }
            'v' => {
                units.push(0x0B);
                i += 1;
            }
            'x' => {
                let h: String = chars[i + 1..(i + 3).min(chars.len())].iter().collect();
                if let Ok(v) = u32::from_str_radix(&h, 16) {
                    push_scalar(&mut units, v);
                }
                i += 3;
            }
            'u' => {
                if chars.get(i + 1) == Some(&'{') {
                    let mut j = i + 2;
                    let mut v: u32 = 0;
                    while j < chars.len() && chars[j] != '}' {
                        v = v
                            .saturating_mul(16)
                            .saturating_add(chars[j].to_digit(16).unwrap_or(0));
                        j += 1;
                    }
                    push_scalar(&mut units, v);
                    i = j + 1;
                } else {
                    let h: String = chars[i + 1..(i + 5).min(chars.len())].iter().collect();
                    if let Ok(v) = u32::from_str_radix(&h, 16) {
                        push_scalar(&mut units, v);
                    }
                    i += 5;
                }
            }
            '\n' | '\u{2028}' | '\u{2029}' => {
                i += 1; // line continuation
            }
            '\r' => {
                i += 1;
                if chars.get(i) == Some(&'\n') {
                    i += 1;
                }
            }
            '0'..='7' => {
                // octal escape: value up to 3 digits
                let mut v: u32 = 0;
                let mut n = 0;
                while n < 3
                    && i < chars.len()
                    && ('0'..='7').contains(&chars[i])
                    && (n == 0 || v * 8 + 7 <= 255)
                {
                    v = v * 8 + chars[i].to_digit(8).unwrap_or(0);
                    i += 1;
                    n += 1;
                }
                units.push(v as u16);
            }
            other => {
                let mut buf = [0u16; 2];
                units.extend_from_slice(other.encode_utf16(&mut buf));
                i += 1;
            }
        }
    }
    // Valid pairs compose; a lone surrogate makes the key unrepresentable.
    String::from_utf16(&units).ok()
}
