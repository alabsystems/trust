//! `TsCore` — the defunctionalized core calculus that is the SOLE product of
//! touching the TypeScript AST.
//!
//! Single-image discipline: every downstream artifact (the `VerifiableFunction` for
//! the ay/SmtBacked path, and later the Clean term for the kernel/Certified path) is
//! a total function of `TsCore`, so a refinement proof and a kernel certificate are
//! provably about the *same* TS program. `TsCore` reuses `trust_types::BinOp`/`Ty`
//! verbatim (one vocabulary, no parallel enum).
//!
//! The fragment is deliberately the deterministic integer core a terminal reducer
//! inhabits: integer literals, variables, binary ops, and a single `If` *expression*
//! (into which `Math.min`/`Math.max`, `a || b`, and `c ? t : e` all elaborate). It
//! is expression-oriented precisely so the `VerifiableFunction` deriver can turn
//! `If` into a `SwitchInt`+`Goto` diamond (there is no `Select` rvalue).

use serde::{Deserialize, Serialize};
use trust_types::{BinOp, Ty};

/// A type in the admitted fragment. `Num{width,signed}` is the *gated* `number` —
/// admitted only after a range proof bounds it to the width (the gate lives in
/// elaboration, not here); `Bool` is direct.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TsTy {
    Num { width: u32, signed: bool },
    Bool,
    /// A fixed-length array of unsigned `elem_width`-bit elements (`number[]` of a
    /// known length). Admitted via the denotational path (`Sort::Array` + `Select`)
    /// — array reducers (`arrayMax`, `clampEach`, table lookups) are in-fragment.
    Arr { elem_width: u32, len: u32 },
}

impl TsTy {
    /// Unsigned integer of `width` bits.
    #[must_use]
    pub fn uint(width: u32) -> Self {
        TsTy::Num { width, signed: false }
    }

    /// Signed (two's-complement) integer of `width` bits.
    #[must_use]
    pub fn sint(width: u32) -> Self {
        TsTy::Num { width, signed: true }
    }

    /// A fixed-length array of unsigned `elem_width`-bit elements.
    #[must_use]
    pub fn array(elem_width: u32, len: u32) -> Self {
        TsTy::Arr { elem_width, len }
    }

    /// The corresponding `trust_types::Ty`. Arrays lower only via the denotational
    /// path; this placeholder is never relied on there (the VerifiableFunction
    /// deriver fails closed on an array — see `lower_function`).
    #[must_use]
    pub fn to_ty(self) -> Ty {
        match self {
            TsTy::Bool => Ty::Bool,
            TsTy::Num { width, signed } => Ty::Int { width, signed },
            TsTy::Arr { elem_width, .. } => Ty::Int { width: elem_width, signed: false },
        }
    }
}

/// A named place in the lowered program — a parameter, a binding, or a resolved
/// member chain (`this._activeBuffer.scrollBottom`). The name is preserved so the
/// derived `VerifiableFunction`'s `LocalDecl.name` matches the symmetric Rust leg,
/// which lets the name/Ty-aware `SimulationRelation` align the two images.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TsVar {
    pub name: String,
    pub ty: TsTy,
}

impl TsVar {
    #[must_use]
    pub fn new(name: impl Into<String>, ty: TsTy) -> Self {
        Self { name: name.into(), ty }
    }
}

/// An expression. `If` is the universal conditional: `Math.min(a,b)` elaborates to
/// `If(a<=b, a, b)`, `a || b` (integer) to `If(a != 0, a, b)`, `c ? t : e` directly.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TsExpr {
    /// An integer literal of the given type.
    Int(i128, TsTy),
    /// A boolean literal.
    Bool(bool),
    /// A variable reference.
    Var(TsVar),
    /// A binary op (arithmetic or comparison). `op` is a `trust_types::BinOp`.
    Bin { op: BinOp, lhs: Box<TsExpr>, rhs: Box<TsExpr>, ty: TsTy },
    /// The universal conditional expression; both arms share `ty`, `cond` is Bool.
    If { cond: Box<TsExpr>, then_e: Box<TsExpr>, else_e: Box<TsExpr>, ty: TsTy },
    /// `base[index]` — a constant-index read of an array variable. The result is an
    /// `elem_width`-bit unsigned number.
    Index { base: String, elem_width: u32, index: u32 },
    /// `base[index_var]` — a read of an array variable indexed by a scalar
    /// variable. Inside a `ForRange` body the index variable is the (bounded) loop
    /// counter, so each unrolled iteration resolves it to a constant `Index`.
    IndexVar { base: String, elem_width: u32, index_var: String },
    /// `obj.field` — a field read of a record/object variable. A record is a bundle
    /// of independent named fields; each `obj.field` is an `elem_width`-bit unsigned
    /// symbolic value (modeled as a distinct variable `obj.field`).
    Field { obj: String, field: String, elem_width: u32 },
    /// `base[index]` with a DATA-DEPENDENT index expression (e.g. `a[min(j,3)]`).
    /// The index must evaluate in-bounds for a faithful read.
    IndexExpr { base: String, elem_width: u32, index: Box<TsExpr> },
    /// `func(args)` — a call to another in-fragment function (composition). Resolved
    /// by inlining the callee's denotation at the call site. The callee must be a
    /// single-`return`-expression function in the same module.
    Call { func: String, args: Vec<TsExpr> },
}

impl TsExpr {
    /// The result type of this expression.
    #[must_use]
    pub fn ty(&self) -> TsTy {
        match self {
            TsExpr::Int(_, ty) | TsExpr::Bin { ty, .. } | TsExpr::If { ty, .. } => *ty,
            TsExpr::Bool(_) => TsTy::Bool,
            TsExpr::Var(v) => v.ty,
            TsExpr::Index { elem_width, .. }
            | TsExpr::IndexVar { elem_width, .. }
            | TsExpr::Field { elem_width, .. }
            | TsExpr::IndexExpr { elem_width, .. } => TsTy::uint(*elem_width),
            // A call returns the fragment's `number` (resolved by inlining). The
            // exact width comes from the callee at denote/eval time.
            TsExpr::Call { .. } => TsTy::uint(16),
        }
    }

    /// `base[index_expr]` — a data-dependent array read.
    #[must_use]
    pub fn index_expr(base: impl Into<String>, elem_width: u32, index: TsExpr) -> TsExpr {
        TsExpr::IndexExpr { base: base.into(), elem_width, index: Box::new(index) }
    }

    /// `obj.field` as an `elem_width`-bit unsigned record-field read.
    #[must_use]
    pub fn field(obj: impl Into<String>, field: impl Into<String>, elem_width: u32) -> TsExpr {
        TsExpr::Field { obj: obj.into(), field: field.into(), elem_width }
    }

    /// `base[index]` as an `elem_width`-bit unsigned element.
    #[must_use]
    pub fn index(base: impl Into<String>, elem_width: u32, index: u32) -> TsExpr {
        TsExpr::Index { base: base.into(), elem_width, index }
    }

    /// `base[index_var]` — array read by a scalar (loop) variable.
    #[must_use]
    pub fn index_var(base: impl Into<String>, elem_width: u32, index_var: impl Into<String>) -> TsExpr {
        TsExpr::IndexVar { base: base.into(), elem_width, index_var: index_var.into() }
    }

    /// `Math.min(a, b)` as an `If` expression (the deriver turns it into a diamond).
    #[must_use]
    pub fn min(a: TsExpr, b: TsExpr, ty: TsTy) -> TsExpr {
        let cond = TsExpr::Bin {
            op: BinOp::Le,
            lhs: Box::new(a.clone()),
            rhs: Box::new(b.clone()),
            ty: TsTy::Bool,
        };
        TsExpr::If { cond: Box::new(cond), then_e: Box::new(a), else_e: Box::new(b), ty }
    }

    /// `Math.max(a, b)` as an `If` expression.
    #[must_use]
    pub fn max(a: TsExpr, b: TsExpr, ty: TsTy) -> TsExpr {
        let cond = TsExpr::Bin {
            op: BinOp::Ge,
            lhs: Box::new(a.clone()),
            rhs: Box::new(b.clone()),
            ty: TsTy::Bool,
        };
        TsExpr::If { cond: Box::new(cond), then_e: Box::new(a), else_e: Box::new(b), ty }
    }
}

/// A statement. The body of a `TsFunction` is a straight-line sequence ending in a
/// `Return`; control flow lives inside `If` *expressions* (kept simple on purpose).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TsStmt {
    /// `const v = e;` / `let v = e;` / `v = e;`
    Assign { var: TsVar, value: TsExpr },
    /// `return e;`
    Return { value: TsExpr },
    /// `for (let var = 0; var < count; var++) { body }` — a STATICALLY-bounded loop.
    /// Semantics are full unrolling: `count` copies of `body` with `var` bound to
    /// `0..count` in turn (so an accumulator threaded through `Assign` reduces over
    /// the range). Out-of-fragment loops (data-dependent bound, `break`) never reach
    /// here — they fail closed at elaboration.
    ForRange { var: String, count: u32, body: Vec<TsStmt> },
}

/// A first-order function over the integer fragment.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TsFunction {
    pub name: String,
    pub def_path: String,
    /// Parameters, in order → `VerifiableFunction` locals `1..=arg_count`.
    pub params: Vec<TsVar>,
    pub body: Vec<TsStmt>,
    pub ret: TsTy,
}
