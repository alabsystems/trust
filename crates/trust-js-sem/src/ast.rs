// AST for the bootstrap slice. Function literals carry parse-time hoisting
// facts (var names, directly nested function declarations, whether the body
// mentions `arguments`) so calls do not re-walk bodies.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::value::Units;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
    Pos,
    /// Bitwise NOT (`~`): ToInt32 complement for Numbers, `-(x+1)` for BigInts.
    BitNot,
    TypeOf,
    Void,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    /// Exponentiation (`**`), right-associative.
    Exp,
    /// Bitwise AND/OR/XOR (`&` `|` `^`).
    BitAnd,
    BitOr,
    BitXor,
    /// Shift left / signed right / unsigned right (`<<` `>>` `>>>`).
    Shl,
    Shr,
    Ushr,
    Lt,
    Le,
    Gt,
    Ge,
    EqLoose,
    NeLoose,
    EqStrict,
    NeStrict,
    InstanceOf,
    In,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogOp {
    And,
    Or,
}

#[derive(Debug, Clone)]
pub enum MemberProp {
    Dot(String),
    Computed(Box<Expr>),
    /// `obj.#name` — a private reference (the bare name, no leading `#`).
    Private(String),
}

/// A destructuring pattern (binding or assignment flavor; assignment
/// patterns may carry `Target` leaves).
#[derive(Debug, Clone)]
pub enum Pattern {
    /// A name leaf: a fresh binding (binding contexts) or an existing
    /// reference (assignment contexts).
    Ident(String),
    /// An assignment-target leaf (member / super-member expressions);
    /// assignment patterns only.
    Target(Rc<Expr>),
    Array {
        /// None = elision (consumes one iterator step).
        elems: Vec<Option<PatElem>>,
        rest: Option<Box<Pattern>>,
    },
    Object {
        props: Vec<(ObjKey, PatElem)>,
        /// Rest target (`...r`); binding flavor restricts it to a name.
        rest: Option<Box<Pattern>>,
    },
}

/// One pattern element with an optional default initializer.
#[derive(Debug, Clone)]
pub struct PatElem {
    pub pat: Pattern,
    pub default: Option<Rc<Expr>>,
}

/// A declaration/parameter binding target: a plain name or a pattern.
#[derive(Debug, Clone)]
pub enum BindTarget {
    Name(String),
    Pattern(Rc<Pattern>),
}

impl BindTarget {
    /// Bound names, in pattern order.
    pub fn bound_names(&self, out: &mut Vec<String>) {
        match self {
            BindTarget::Name(n) => out.push(n.clone()),
            BindTarget::Pattern(p) => pattern_bound_names(p, out),
        }
    }
}

pub fn pattern_bound_names(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Ident(n) => out.push(n.clone()),
        Pattern::Target(_) => {}
        Pattern::Array { elems, rest } => {
            for e in elems.iter().flatten() {
                pattern_bound_names(&e.pat, out);
            }
            if let Some(r) = rest {
                pattern_bound_names(r, out);
            }
        }
        Pattern::Object { props, rest } => {
            for (_, e) in props {
                pattern_bound_names(&e.pat, out);
            }
            if let Some(r) = rest {
                pattern_bound_names(r, out);
            }
        }
    }
}

/// One formal parameter (pattern or name, with an optional default).
#[derive(Debug, Clone)]
pub struct Param {
    pub target: BindTarget,
    pub default: Option<Rc<Expr>>,
}

/// An object-literal property key: fixed, or computed at evaluation.
#[derive(Debug, Clone)]
pub enum ObjKey {
    Fixed(Units),
    Computed(Rc<Expr>),
}

/// One object-literal property definition.
#[derive(Debug, Clone)]
pub enum PropDef {
    /// `key: value` / shorthand / numeric / string keys.
    Data(ObjKey, Expr),
    /// The B.3.1 prototype-mutating `__proto__ : value` colon form. Only
    /// legal when the literal reparses as a pattern (an ordinary property
    /// there); a surviving literal is judged at end of parse.
    ProtoData(Expr),
    /// `key(params) { ... }` shorthand method ([[HomeObject]] = the object).
    Method(ObjKey, Rc<FuncLit>),
    /// `get key() { ... }`
    Getter(ObjKey, Rc<FuncLit>),
    /// `set key(param) { ... }`
    Setter(ObjKey, Rc<FuncLit>),
}

/// A class member key: fixed at parse, computed at class definition, or a
/// private name (the bare name, no leading `#`).
#[derive(Debug, Clone)]
pub enum ClassKey {
    Fixed(Units),
    Computed(Box<Expr>),
    Private(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MethodKind {
    Normal,
    Get,
    Set,
}

/// One class element (besides the constructor, which lives on ClassLit).
#[derive(Debug, Clone)]
pub enum ClassMember {
    Method {
        stat: bool,
        key: ClassKey,
        mk: MethodKind,
        lit: Rc<FuncLit>,
    },
    Field {
        stat: bool,
        key: ClassKey,
        init: Option<Rc<Expr>>,
    },
}

/// A class declaration/expression body.
#[derive(Debug)]
pub struct ClassLit {
    /// The binding name (also the inner immutable self-binding).
    pub name: Option<String>,
    /// NamedEvaluation-inferred name (sets the `name` prop only — no inner
    /// self-binding).
    pub inferred_name: std::cell::RefCell<Option<String>>,
    pub heritage: Option<Box<Expr>>,
    /// The explicit constructor, if any.
    pub ctor: Option<Rc<FuncLit>>,
    pub members: Vec<ClassMember>,
    /// The DISTINCT private names declared in this class body (bare, no `#`),
    /// in source order — one fresh PrivateName is allocated per entry at
    /// ClassDefinitionEvaluation (a get/set pair shares one entry).
    pub private_names: Vec<String>,
}

/// One piece of an (untagged) template literal.
#[derive(Debug, Clone)]
pub enum TplPart {
    Str(Rc<Units>),
    Expr(Box<Expr>),
}

#[derive(Debug, Clone)]
pub enum Expr {
    Num(f64),
    /// A BigInt literal (`123n`, `0x1fn`, ...): the parsed arbitrary-precision
    /// value, shared so cloning the AST never copies digits.
    BigInt(Rc<num_bigint::BigInt>),
    Str(Rc<Units>),
    Bool(bool),
    Null,
    This,
    /// A regular-expression literal `/body/flags` (12.9.5). `body` are the
    /// source code units WITHOUT the enclosing slashes; `flags` are the flag
    /// code units. Pattern validity is validated at parse (an invalid literal
    /// is an early SyntaxError); evaluation creates a fresh RegExp object.
    Regex {
        body: Rc<Units>,
        flags: Rc<Units>,
    },
    Ident(String),
    /// Array literal; None = elision (hole).
    Array(Vec<Option<Expr>>),
    /// The comma operator: evaluate all, value of the last.
    Seq(Vec<Expr>),
    Object(Vec<PropDef>),
    Function(Rc<FuncLit>),
    /// An arrow function (lexical this/arguments/super captured at creation).
    Arrow(Rc<FuncLit>),
    Class(Rc<ClassLit>),
    /// A destructuring assignment: `pattern = value` (value of the whole
    /// expression is the rhs value).
    PatternAssign {
        pat: Rc<Pattern>,
        value: Box<Expr>,
    },
    /// A spread element inside an ARRAY LITERAL (`[...iterable]`) or an
    /// ArgumentList (`f(...args)`): the inner expression is iterated via the
    /// general iterator protocol. Inside an OBJECT literal a `Spread` is object
    /// spread (out of slice) and refuses at end of parse.
    Spread(Box<Expr>),
    /// A trailing comma immediately after a spread/rest element in an array
    /// literal (`[...a,]`): contributes NO element to the array literal (the
    /// literal is exactly `[...a]`), but a reparse as an assignment pattern is
    /// a SyntaxError (a rest element admits no trailing comma). This marker
    /// lets a single AST distinguish `[...a,]` (no hole) from `[...a,,]` (one
    /// hole). It lives only inside array `elems`; evaluation skips it.
    SpreadTrailingComma,
    /// A PARENTHESIZED object/array literal: the grouping operator strips
    /// pattern-conversion eligibility (`({}) = 1` is a pinned SyntaxError),
    /// so the marker survives only around literals.
    Paren(Box<Expr>),
    Template(Vec<TplPart>),
    /// `#x in obj` — the private brand-check operator (13.10
    /// `PrivateIdentifier in ShiftExpression`).
    PrivateIn {
        name: String,
        obj: Box<Expr>,
    },
    /// `super.x` / `super[x]` in a method ([[HomeObject]]-relative).
    SuperMember {
        prop: MemberProp,
    },
    /// `super(...)` in a derived constructor.
    SuperCall {
        args: Vec<Expr>,
    },
    Member {
        obj: Box<Expr>,
        prop: MemberProp,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    New {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    Unary {
        op: UnOp,
        expr: Box<Expr>,
    },
    /// `delete expr` — needs the Reference, so it is not a UnOp.
    Delete(Box<Expr>),
    Update {
        inc: bool,
        prefix: bool,
        target: Box<Expr>,
    },
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Logical {
        op: LogOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Cond {
        test: Box<Expr>,
        cons: Box<Expr>,
        alt: Box<Expr>,
    },
    /// `yield expr` / `yield* expr` / `yield` (only legal inside a generator
    /// body). The operand is None for a bare `yield`. `delegate` marks
    /// `yield*`.
    Yield {
        delegate: bool,
        arg: Option<Box<Expr>>,
    },
    /// `await UnaryExpression` (only legal inside an async function/arrow/
    /// method body). Suspends the async execution until the awaited value's
    /// promise settles.
    Await(Box<Expr>),
    Assign {
        /// None = plain `=`; Some(op) = compound (`+=` etc.).
        op: Option<BinOp>,
        target: Box<Expr>,
        value: Box<Expr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    Var,
    Let,
    Const,
}

#[derive(Debug, Clone)]
pub enum ForInit {
    Var(Vec<(BindTarget, Option<Expr>)>),
    /// `for (let/const x = ..., y = ...; ; )` — a fresh loop scope with
    /// per-iteration copies for `let` (CreatePerIterationEnvironment).
    Lex {
        is_const: bool,
        decls: Vec<(BindTarget, Option<Expr>)>,
    },
    Expr(Expr),
}

/// The left-hand side of a for-in / for-of head.
#[derive(Debug, Clone)]
pub enum ForInOfLeft {
    /// `for (var x in ...)` (name or pattern binding).
    Var(BindTarget),
    /// `for (let x in ...)` / `for (const x in ...)`; true = const.
    Lex(BindTarget, bool),
    /// `for (x in ...)` / `for (o.p in ...)` — an existing reference.
    Target(Expr),
    /// `for ([a, b] of ...)` — a destructuring assignment per iteration.
    TargetPattern(Rc<Pattern>),
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Expr(Expr),
    VarDecl {
        kind: DeclKind,
        decls: Vec<(BindTarget, Option<Expr>)>,
    },
    FuncDecl(Rc<FuncLit>),
    ClassDecl {
        name: String,
        class: Rc<ClassLit>,
    },
    Empty,
    Block(Vec<Stmt>),
    If {
        test: Expr,
        cons: Box<Stmt>,
        alt: Option<Box<Stmt>>,
    },
    While {
        test: Expr,
        body: Box<Stmt>,
    },
    DoWhile {
        body: Box<Stmt>,
        test: Expr,
    },
    For {
        init: Option<ForInit>,
        test: Option<Expr>,
        update: Option<Expr>,
        body: Box<Stmt>,
    },
    ForIn {
        left: ForInOfLeft,
        obj: Expr,
        body: Box<Stmt>,
    },
    ForOf {
        left: ForInOfLeft,
        expr: Expr,
        body: Box<Stmt>,
    },
    Return(Option<Expr>),
    Throw(Expr),
    Break,
    Continue,
    Try {
        block: Vec<Stmt>,
        /// (param, body); param None for `catch {}`.
        catch: Option<(Option<BindTarget>, Vec<Stmt>)>,
        finally: Option<Vec<Stmt>>,
    },
    Switch {
        disc: Expr,
        /// (test, statements); test None = default clause.
        cases: Vec<(Option<Expr>, Vec<Stmt>)>,
    },
}

/// A function literal (declaration or expression) with hoisting facts.
#[derive(Debug)]
pub struct FuncLit {
    /// Declared/bound name; None for anonymous expressions (NamedEvaluation
    /// may still supply an inferred `name` own property).
    pub name: Option<String>,
    /// True when `name` came from NamedEvaluation (no self-binding scope).
    pub inferred_name: bool,
    pub params: Vec<Param>,
    /// `...rest` parameter, if any (always makes the list non-simple).
    pub rest_param: Option<BindTarget>,
    /// All parameters are plain names without defaults (drives arguments-
    /// object mapping).
    pub simple_params: bool,
    pub body: Vec<Stmt>,
    pub strict: bool,
    /// var-declared names anywhere in the body (not inside nested functions).
    pub vars: Vec<String>,
    /// Function declarations at the top level of the body, in source order.
    pub funcs: Vec<Rc<FuncLit>>,
    /// The body mentions `arguments` AND no parameter shadows it (so an
    /// arguments object is created at call time; mapped in sloppy code,
    /// unmapped in strict).
    pub uses_arguments: bool,
    /// A MethodDefinition function (accessor/class method): no own
    /// `prototype`, not a constructor, and no legacy caller/arguments own
    /// surface.
    pub is_method: bool,
    /// An arrow function: lexical this/arguments/super, never a constructor.
    /// (Behavior routes through FnImpl::Arrow; the flag documents the
    /// literal's provenance.)
    #[allow(dead_code)]
    pub is_arrow: bool,
    /// A generator function/method (`function*` / `*m(){}`): calling it
    /// creates a generator object (suspendedStart) rather than running the
    /// body, and `yield`/`yield*` inside the body are YieldExpressions.
    pub is_generator: bool,
    /// An async function/method/arrow (`async function` / `async m(){}` /
    /// `async () => {}`): calling it runs the body synchronously up to the
    /// first `await`, returns a promise, and suspends on `await` via the same
    /// resumable machine that drives generators. `await` inside the body is an
    /// AwaitExpression. Async generators (`async function*`) are out of slice.
    pub is_async: bool,
}

/// A parsed script (one harness include, or the test body).
#[derive(Debug)]
pub struct Program {
    pub body: Vec<Stmt>,
    pub strict: bool,
    pub vars: Vec<String>,
    pub funcs: Vec<Rc<FuncLit>>,
}
