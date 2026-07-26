// trust-js-parse: AST node types for the ES2025 Script grammar.
//
// The AST is opaque to the parse-verdict lane (M1 D1) and grows toward the
// tier-0 interpreter's needs (M1 D2). Numeric literals keep their raw source
// text so every node stays `Eq`-derivable (the frozen `ParseOutcome` derives
// `Eq`); the interpreter numericizes later.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// Kind of a variable declaration statement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    Var,
    Let,
    Const,
    /// Explicit-resource-management `using x = …` (lexical, ident-only).
    Using,
    /// `await using x = …` (async contexts).
    AwaitUsing,
}

/// Binding / assignment pattern (used for declarations, parameters, catch
/// bindings, and destructuring assignment after cover reparse).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pat {
    Ident(String),
    /// Assignment-pattern target that is a member expression (destructuring
    /// assignment only, never bindings).
    Expr(Box<Expr>),
    Array {
        /// `None` = elision hole.
        elems: Vec<Option<Pat>>,
        rest: Option<Box<Pat>>,
    },
    Object {
        props: Vec<ObjPatProp>,
        rest: Option<Box<Pat>>,
    },
    /// Pattern with a default initializer.
    Default(Box<Pat>, Box<Expr>),
    /// Rest parameter/element (`...pat`) in formal parameter lists.
    Rest(Box<Pat>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjPatProp {
    pub key: PropKey,
    /// The bound pattern (for shorthand this is the same identifier).
    pub value: Pat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropKey {
    Ident(String),
    Str(String),
    Num(String),
    Computed(Box<Expr>),
    Private(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Func {
    pub name: Option<String>,
    pub params: Vec<Pat>,
    pub body: Vec<Stmt>,
    /// Concise arrow body (`x => expr`).
    pub expr_body: Option<Box<Expr>>,
    pub is_async: bool,
    pub is_gen: bool,
    pub is_arrow: bool,
    pub strict: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Class {
    pub name: Option<String>,
    pub heritage: Option<Box<Expr>>,
    pub elements: Vec<ClassElement>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MethodKind {
    Method,
    Get,
    Set,
    Constructor,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassElement {
    Method {
        is_static: bool,
        kind: MethodKind,
        key: PropKey,
        func: Func,
    },
    Field {
        is_static: bool,
        key: PropKey,
        init: Option<Expr>,
    },
    StaticBlock(Vec<Stmt>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjProp {
    /// `key: value` (`was_proto`: non-computed `__proto__` in this form).
    KeyValue { key: PropKey, value: Expr },
    /// Shorthand `{ a }`.
    Shorthand(String),
    /// Cover-only `{ a = expr }` — legal solely when the literal is reparsed
    /// as a pattern; the parser tracks the pending error.
    CoverInit(String, Box<Expr>),
    Method { kind: MethodKind, key: PropKey, func: Func },
    Spread(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Ident(String),
    This,
    Null,
    Bool(bool),
    Num(String),
    BigInt(String),
    Str {
        raw: String,
        any_escape: bool,
        /// Contains a legacy octal / \8 \9 escape (retro-checked when a
        /// directive prologue turns the body strict).
        octal: bool,
    },
    Regex {
        pattern: String,
        flags: String,
    },
    Template {
        /// Raw text pieces (n+1 for n substitutions).
        quasis: Vec<String>,
        exprs: Vec<Expr>,
    },
    TaggedTemplate {
        tag: Box<Expr>,
        quasis: Vec<String>,
        exprs: Vec<Expr>,
    },
    Array {
        /// `None` = elision hole; spread elements are `Arg::Spread`.
        elems: Vec<Option<Arg>>,
        /// A trailing comma followed the last element (matters for the
        /// rest-must-be-last rule under pattern conversion).
        trailing_comma: bool,
    },
    Object(Vec<ObjProp>),
    Function(Func),
    Arrow(Func),
    Class(Class),
    Paren(Box<Expr>),
    /// Comma sequence.
    Seq(Vec<Expr>),
    Unary {
        op: &'static str,
        arg: Box<Expr>,
    },
    Update {
        op: &'static str,
        prefix: bool,
        arg: Box<Expr>,
    },
    Binary {
        op: &'static str,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Logical {
        op: &'static str,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Assign {
        op: &'static str,
        /// Pattern for destructuring, `Pat::Expr`/`Pat::Ident` for simple.
        target: Box<Pat>,
        value: Box<Expr>,
    },
    Cond {
        test: Box<Expr>,
        cons: Box<Expr>,
        alt: Box<Expr>,
    },
    Member {
        obj: Box<Expr>,
        prop: Box<PropKey>,
        /// `?.` somewhere in this link.
        optional: bool,
        /// This member expression is part of an optional chain.
        in_chain: bool,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Arg>,
        optional: bool,
        in_chain: bool,
    },
    New {
        callee: Box<Expr>,
        args: Vec<Arg>,
    },
    NewTarget,
    /// `import.meta` (module goal only).
    ImportMeta,
    ImportCall(Vec<Expr>),
    SuperProp(Box<PropKey>),
    SuperCall(Vec<Arg>),
    Yield {
        arg: Option<Box<Expr>>,
        delegate: bool,
    },
    Await(Box<Expr>),
    /// `#x in obj` — the private-name side.
    PrivateRef(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Arg {
    Expr(Expr),
    Spread(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForInit {
    Decl(DeclKind, Vec<(Pat, Option<Expr>)>),
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForHead {
    Decl(DeclKind, Pat),
    Pat(Pat),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchCase {
    /// `None` = default clause.
    pub test: Option<Expr>,
    pub body: Vec<Stmt>,
}

// ---- module goal: import / export declarations (ECMA-262 §16.2) ----------

/// A `ModuleExportName` — either an `IdentifierName` or a `StringLiteral`
/// (arbitrary-module-namespace-names). String forms carry the cooked value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleExportName {
    Ident(String),
    Str(String),
}

/// One named-import specifier: `imported [as local]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportEntry {
    /// The name exported by the source module.
    pub imported: ModuleExportName,
    /// The local binding introduced in this module.
    pub local: String,
}

/// `import ImportClause FromClause ;` / `import ModuleSpecifier ;`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl {
    /// `import d from …` default binding.
    pub default: Option<String>,
    /// `import * as ns from …` namespace binding.
    pub namespace: Option<String>,
    /// `import { a, b as c } from …` named imports.
    pub named: Vec<ImportEntry>,
    /// The module specifier (cooked string value).
    pub source: String,
}

/// One export specifier: `local [as exported]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportEntry {
    /// The local (or, with a FromClause, source-module) name.
    pub local: ModuleExportName,
    /// The externally visible export name.
    pub exported: ModuleExportName,
}

/// The several `export` declaration shapes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExportDecl {
    /// `export * from 'mod'` (alias `None`) / `export * as x from 'mod'`.
    Star {
        alias: Option<ModuleExportName>,
        source: String,
    },
    /// `export { … }` with an optional `from 'mod'` re-export clause.
    Named {
        specs: Vec<ExportEntry>,
        source: Option<String>,
    },
    /// `export VariableStatement | Declaration` (the wrapped declaration).
    Decl(Box<Stmt>),
    /// `export default HoistableDeclaration | ClassDeclaration |
    /// AssignmentExpression` (wrapped as `FuncDecl` / `ClassDecl` / `Expr`).
    Default(Box<Stmt>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Expr(Expr),
    Block(Vec<Stmt>),
    Empty,
    Debugger,
    Decl {
        kind: DeclKind,
        decls: Vec<(Pat, Option<Expr>)>,
    },
    If {
        test: Expr,
        cons: Box<Stmt>,
        alt: Option<Box<Stmt>>,
    },
    DoWhile {
        body: Box<Stmt>,
        test: Expr,
    },
    While {
        test: Expr,
        body: Box<Stmt>,
    },
    For {
        init: Option<ForInit>,
        test: Option<Expr>,
        update: Option<Expr>,
        body: Box<Stmt>,
    },
    ForIn {
        left: ForHead,
        right: Expr,
        body: Box<Stmt>,
    },
    ForOf {
        left: ForHead,
        right: Expr,
        body: Box<Stmt>,
        is_await: bool,
    },
    Continue(Option<String>),
    Break(Option<String>),
    Return(Option<Expr>),
    With {
        obj: Expr,
        body: Box<Stmt>,
    },
    Labeled {
        label: String,
        body: Box<Stmt>,
    },
    Switch {
        disc: Expr,
        cases: Vec<SwitchCase>,
    },
    Throw(Expr),
    Try {
        block: Vec<Stmt>,
        catch: Option<(Option<Pat>, Vec<Stmt>)>,
        finally: Option<Vec<Stmt>>,
    },
    FuncDecl(Func),
    ClassDecl(Class),
    /// `import` declaration (module goal, top level only).
    Import(ImportDecl),
    /// `export` declaration (module goal, top level only).
    Export(ExportDecl),
}
