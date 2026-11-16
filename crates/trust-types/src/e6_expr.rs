//! The E6-ONLY body reader's module (E6 admission expansion, design note
//! `docs/design-notes/2026-09-28-e6-admission-expansion.md` §5).
//!
//! # Why a separate module, and not a widening of `admissible_body`
//!
//! [`crate::admissible_body::recognize_admissible_body`] is also side B of the
//! Clean-origin faithfulness gate, and there is a standing prohibition on
//! editing side B's producers (`crates/trust-clean-origin/src/emit.rs`,
//! `compiler/rustc_mir_transform/src/clean_origin_mir.rs`): doing so "converts
//! the gate from a semantics check into a round trip". So every E6 widening
//! lands here, as a reader that the E6 importer
//! (`trust_certify::clean_island::admit_function_into`) consults only after the
//! existing chain answers `None` — the same pattern island forwarding uses.
//! The composed Boolean Clean-origin slice now reuses this independently
//! authored reader unchanged through the canonical E6 importer. Its own
//! emitter grammar is bounded and its gate compares the actual emitted
//! body's image with the original declaration. This reader and its renderer
//! remain frozen against that consumer; the older primitive routes are unchanged.
//!
//! # What lives here today
//!
//! * [`read_e6_body`] — THE E6-ONLY READER. Its typed AST is [`E6Expr`]. It
//!   reads, in order: the single I1′ node, `==`/`!=` over two `bool`
//!   parameters ([`E6Expr::BoolCmp`], minted by
//!   `trust_spec_elab::admit_bool_cmp_function`); then, since I3′, a `bool`
//!   CONNECTIVE TREE ([`E6Expr::Tree`], the [`tree`] module, minted by
//!   `trust_spec_elab::admit_e6_tree_function`) — `&&`/`||` as rustc's
//!   short-circuit control flow, `!`, `&`/`|`/`^` over `bool`, and
//!   comparisons of parameters and literals as leaves. What it reads becomes a
//!   kernel defining equation, so its reading is in the trusted base
//!   (`docs/TCB.md`, `EnsuresCitationDischarge`). The differential harness
//!   `crates/trust-certify/tests/e6_differential.rs` executes a fixture row
//!   of every carrier it admits against the Rust body — `bool`/`u8`/`i8`/
//!   `u16`/`i16` exhaustively, `u32`/`i32`/`u64`/`i64`/`i128` on a fixed
//!   sample (the [`tree`] module docs say which rows).
//! * [`first_construct_outside_fragment`] (increment I0) — DIAGNOSTICS ONLY:
//!   the MIR construct that keeps a body out of every E6 reader, named for the
//!   refusal a user sees. No verdict, mint or facet reads it.

use crate::{
    BasicBlock, BinOp, BlockId, ConstValue, Operand, Rvalue, Statement, Terminator, Ty, UnOp,
    VerifiableFunction,
};

pub mod tree;

pub use tree::{E6Carrier, E6Cmp, E6Term, normalize_bool, read_e6_tree};

/// A short Rust spelling of a scalar type, for diagnostics.
#[must_use]
pub fn ty_spelling(ty: &Ty) -> String {
    match ty {
        Ty::Bool => "bool".to_owned(),
        Ty::Int { width, signed: true } => format!("i{width}"),
        Ty::Int { width, signed: false } => format!("u{width}"),
        Ty::PtrSizedInt { signed: true } => "isize".to_owned(),
        Ty::PtrSizedInt { signed: false } => "usize".to_owned(),
        Ty::Char => "char".to_owned(),
        Ty::Float { width } => format!("f{width}"),
        Ty::Ref { mutable: false, inner } => format!("&{}", ty_spelling(inner)),
        Ty::Ref { mutable: true, inner } => format!("&mut {}", ty_spelling(inner)),
        Ty::Unit => "()".to_owned(),
        _ => "a non-scalar type".to_owned(),
    }
}

fn local_ty(func: &VerifiableFunction, local: usize) -> Option<&Ty> {
    if let Some(decl) = func.body.locals.get(local)
        && decl.index == local
    {
        return Some(&decl.ty);
    }
    func.body.locals.iter().find(|l| l.index == local).map(|l| &l.ty)
}

/// The type an operand carries, spelled for a diagnostic, when it is knowable
/// from the body alone.
fn operand_ty(func: &VerifiableFunction, op: &Operand) -> Option<String> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            local_ty(func, p.local).map(ty_spelling)
        }
        Operand::Copy(_) | Operand::Move(_) => None,
        Operand::Constant(ConstValue::Bool(_)) => Some("bool".to_owned()),
        Operand::Constant(ConstValue::Uint(_, width)) => Some(format!("u{width}")),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => None,
    }
}

fn binop_spelling(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Cmp => "cmp",
    }
}

/// How early a finding is reported when a body carries several. The CAUSE a
/// user can act on comes first: a loop or a call outranks the operator inside
/// it, and a compiler-inserted cast of a literal (the `1_i32 as u32` rustc
/// emits for a shift amount) or an overflow `Assert` ranks after the operator
/// that caused it, so `v << 1` is reported as the shift, not as its guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Rank {
    Loop,
    Call,
    Operator,
    Cast,
    Branch,
    Assert,
    ConstantCast,
    Other,
}

struct Finding {
    rank: Rank,
    what: String,
}

fn operator_finding(
    func: &VerifiableFunction,
    op: BinOp,
    l: &Operand,
    r: &Operand,
) -> Option<String> {
    let ty = operand_ty(func, l).or_else(|| operand_ty(func, r));
    let on = ty.as_deref().map_or_else(String::new, |t| format!(" on `{t}`"));
    let sym = binop_spelling(op);
    let is_bool = ty.as_deref() == Some("bool");
    Some(match op {
        // Trust (E6 expansion I3′): `&`/`|`/`^` over `bool` are connectives the
        // tree reader reads.
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor if is_bool => return None,
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
            format!("the bit operation `{sym}` (`BinOp::{op:?}`){on}")
        }
        BinOp::Shl | BinOp::Shr => format!("the shift `{sym}` (`BinOp::{op:?}`){on}"),
        BinOp::Div | BinOp::Rem => format!("the division `{sym}` (`BinOp::{op:?}`){on}"),
        BinOp::Add | BinOp::Sub | BinOp::Mul => format!(
            "the raw arithmetic `{sym}` (`BinOp::{op:?}`){on}: E6 reads only the \
             marker-authenticated `wrapping_add`/`_sub`/`_mul` calls"
        ),
        // `==`/`!=` over `bool` are read by `read_e6_body` (I1′), and since
        // I3′ `!=` over integers is a comparison leaf of the tree reader: a
        // leaf, not a construct outside the fragment.
        BinOp::Eq | BinOp::Ne => return None,
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge if is_bool => {
            format!("the ordering comparison `{sym}` (`BinOp::{op:?}`) on `bool`")
        }
        BinOp::Cmp => format!("the three-way `cmp` (`BinOp::Cmp`){on}"),
        // `<`/`<=`/`==`/`>`/`>=` over integers are comparison LEAVES every
        // comparison shape reads; on their own they keep nothing out.
        _ => return None,
    })
}

fn rvalue_finding(func: &VerifiableFunction, rvalue: &Rvalue) -> Option<Finding> {
    let (rank, what) = match rvalue {
        Rvalue::BinaryOp(op, l, r) => (Rank::Operator, operator_finding(func, *op, l, r)?),
        Rvalue::CheckedBinaryOp(op, l, r) => {
            let on = operand_ty(func, l)
                .or_else(|| operand_ty(func, r))
                .map_or_else(String::new, |t| format!(" on `{t}`"));
            (
                Rank::Operator,
                format!(
                    "the overflow-checked `{}` (`CheckedBinaryOp({op:?})`){on}, whose overflow \
                     `Assert` is a panic path",
                    binop_spelling(*op)
                ),
            )
        }
        Rvalue::UncheckedBinaryOp(op, ..) => (
            Rank::Operator,
            format!(
                "the unchecked `{}` (`UncheckedBinaryOp({op:?})`, undefined behaviour on \
                 overflow)",
                binop_spelling(*op)
            ),
        ),
        Rvalue::UnaryOp(op, x) => {
            let on = operand_ty(func, x).map_or_else(String::new, |t| format!(" on `{t}`"));
            let what = match op {
                // Trust (E6 expansion I3′): `!` over `bool` is a connective.
                UnOp::Not if operand_ty(func, x).as_deref() == Some("bool") => return None,
                UnOp::Not => format!("the negation `!` (`UnOp::Not`){on}"),
                UnOp::Neg => format!("the arithmetic negation `-` (`UnOp::Neg`){on}"),
                _ => format!("the unary operation `{op:?}`{on}"),
            };
            (Rank::Operator, what)
        }
        Rvalue::Cast(Operand::Constant(_), to) => (
            Rank::ConstantCast,
            format!(
                "a cast of a literal to `{}` (e.g. an inline `CONST as {}`)",
                ty_spelling(to),
                ty_spelling(to)
            ),
        ),
        Rvalue::Cast(from, to) => {
            let from = operand_ty(func, from).unwrap_or_else(|| "?".to_owned());
            (Rank::Cast, format!("the cast `{from} as {}`", ty_spelling(to)))
        }
        Rvalue::Ref { .. } | Rvalue::AddressOf(..) => (Rank::Other, "a borrow".to_owned()),
        Rvalue::Discriminant(_) => (Rank::Other, "an enum discriminant read".to_owned()),
        Rvalue::Len(_) => (Rank::Other, "a slice length read".to_owned()),
        Rvalue::Repeat(..) => (Rank::Other, "an array repeat expression".to_owned()),
        Rvalue::PtrOffset { .. } => (Rank::Other, "a pointer offset".to_owned()),
        Rvalue::Unsupported { kind, .. } => {
            (Rank::Other, format!("an rvalue the extractor does not model (`{kind}`)"))
        }
        // `Use`, `Aggregate` and `CopyForDeref` are the plumbing of admitted
        // shapes; on their own they keep nothing out.
        _ => return None,
    };
    Some(Finding { rank, what })
}

fn block_index(func: &VerifiableFunction, id: BlockId) -> Option<usize> {
    if func.body.blocks.get(id.0).is_some_and(|b| b.id == id) {
        return Some(id.0);
    }
    func.body.blocks.iter().position(|b| b.id == id)
}

/// The first back edge of a depth-first walk from the entry block, as
/// `(from, to)` block ids.
fn first_back_edge(func: &VerifiableFunction) -> Option<(BlockId, BlockId)> {
    let blocks = &func.body.blocks;
    if blocks.is_empty() {
        return None;
    }
    // 0 = unvisited, 1 = on the stack, 2 = done.
    let mut state = vec![0u8; blocks.len()];
    let mut stack: Vec<(usize, usize)> = vec![(0, 0)];
    state[0] = 1;
    while let Some(top) = stack.last_mut() {
        let (at, edge_idx) = *top;
        if let Some(to) =
            crate::structural_termination::terminator_successor_at(&blocks[at].terminator, edge_idx)
        {
            top.1 += 1;
            let Some(ti) = block_index(func, to) else { continue };
            match state[ti] {
                0 => {
                    state[ti] = 1;
                    stack.push((ti, 0));
                }
                1 => return Some((blocks[at].id, to)),
                _ => {}
            }
        } else {
            state[at] = 2;
            stack.pop();
        }
    }
    None
}

fn is_read_primitive_call(callee: &str) -> bool {
    crate::admissible_body::PrimitiveCallee::classify(callee).is_some()
        || crate::RustcCheckedPrimitiveMethod::classify(callee).is_some()
        || tree::wrapping_primitive(callee).is_some()
        || tree::checked_primitive(callee).is_some()
}

/// The scrutinee types whose multi-target `switchInt` the tree reader reads
/// AND the tree producer mints (`u128` is read but has no decision image).
const TREE_SWITCH_CARRIERS: [&str; 10] =
    ["bool", "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "i128"];

fn terminator_finding(func: &VerifiableFunction, block: &BasicBlock) -> Option<Finding> {
    let (rank, what) = match &block.terminator {
        Terminator::Call { func: callee, .. } | Terminator::TailCall { func: callee, .. } => {
            if is_read_primitive_call(callee) {
                return None;
            }
            (
                Rank::Call,
                format!(
                    "the call to `{callee}` (E6 reads only the marker-authenticated \
                     `wrapping_*`/signed `checked_*` core methods and a forwarding call to a \
                     Clean island definition)"
                ),
            )
        }
        // Trust (E6 expansion I4′): a multi-target `switchInt` on a `bool` or
        // integer carrier the tree producer mints (`u8`..`u64`, `i8`..`i128`)
        // is a `match` the tree reader reads; one on anything else (a `u128`,
        // whose mint has no decision image; a `char` or a pointer-sized
        // scrutinee the extraction kept) is still named.
        Terminator::SwitchInt { targets, discr, .. } if targets.len() > 1 => {
            let ty = operand_ty(func, discr);
            if ty.as_deref().is_some_and(|t| TREE_SWITCH_CARRIERS.contains(&t)) {
                return None;
            }
            let on = ty.map_or_else(String::new, |t| format!(" on `{t}`"));
            (
                Rank::Branch,
                format!(
                    "a {}-way `switchInt`{on} (a multi-arm `match` or `matches!`)",
                    targets.len() + 1
                ),
            )
        }
        Terminator::Assert { msg, .. } => (
            Rank::Assert,
            format!("an `Assert` (`{msg:?}`), a panic path E6 never imports as a total function"),
        ),
        Terminator::Unreachable => (
            Rank::Branch,
            "an `Unreachable` terminator (an exhaustive `match` without a `_` arm)".to_owned(),
        ),
        Terminator::Drop { .. } => (Rank::Other, "a `Drop`".to_owned()),
        Terminator::Opaque { kind, .. } => {
            (Rank::Other, format!("a terminator the extractor does not model (`{kind}`)"))
        }
        Terminator::Resume => (Rank::Other, "an unwind `Resume`".to_owned()),
        _ => return None,
    };
    Some(Finding { rank, what })
}

/// The MIR construct that keeps `func`'s body out of every E6 reader, spelled
/// for the refusal a user sees — or `None` when every construct in the body is
/// one some shape reads and only their COMPOSITION is outside the fragment.
///
/// DIAGNOSTICS ONLY. Nothing that decides admission, a facet, or a verdict may
/// call this: it is a best-effort explanation over the same body the readers
/// saw, and a wrong answer here costs a misleading sentence, never a proof.
///
/// When a body carries several constructs the one reported is the most
/// actionable (see `Rank`), first in block order among equals, and the count
/// of the rest is appended.
#[must_use]
pub fn first_construct_outside_fragment(func: &VerifiableFunction) -> Option<String> {
    let mut findings: Vec<Finding> = Vec::new();
    if let Some((from, to)) = first_back_edge(func) {
        findings.push(Finding {
            rank: Rank::Loop,
            what: format!("a loop (the back edge bb{} -> bb{})", from.0, to.0),
        });
    }
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                findings.extend(rvalue_finding(func, rvalue));
            }
        }
        findings.extend(terminator_finding(func, block));
    }
    let total = findings.len();
    let best = findings.into_iter().enumerate().min_by_key(|(i, f)| (f.rank, *i))?.1;
    Some(if total > 1 {
        format!("{} (and {} further construct(s) outside it)", best.what, total - 1)
    } else {
        best.what
    })
}

// ---------------------------------------------------------------------------
// THE E6-ONLY READER (increment I1′: `==` and `!=` over `bool`)
// ---------------------------------------------------------------------------

/// An operand of an [`E6Expr::BoolCmp`]: a `bool` PARAMETER (0-based).
///
/// There is no literal leaf. rustc's `InstSimplify` rewrites `a == true` and
/// `false != a` to `a` (a projection the frozen chain reads) and the
/// remaining literal forms to a negation, at both opt levels (MEASURED on the
/// differential harness's dumps), so a literal leaf would be trusted surface
/// that no real MIR reaches.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolLeaf {
    /// A 0-based source parameter whose declared type is `bool`.
    Param(usize),
}

/// The equality a [`E6Expr::BoolCmp`] decides. There is deliberately no
/// ordering variant: `<`/`<=`/`>`/`>=` over `bool` are ORDERINGS
/// (`false < true`), and an `==` image for them would be a false import
/// (review H1 — `a < b` at `(false, true)` is `true`, `a == b` is `false`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolEqOp {
    /// `a == b` — minted as `decide (Eq Bool a b)`.
    Eq,
    /// `a != b` — minted as `Bool.not (decide (Eq Bool a b))`.
    Ne,
}

/// A body the E6-ONLY reader read. The typed AST of design note §5 rule 2
/// (Param, Const, BitOp, Shift, DivRem, Cast, Cmp, BoolOp, Ite, Call) grows
/// here one node per increment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum E6Expr {
    /// `_0 = Eq|Ne(l, r)` over `bool` operands, returned as `bool` (I1′).
    BoolCmp { op: BoolEqOp, left: BoolLeaf, right: BoolLeaf },
    /// A `bool` connective tree (I3′) or a value decision tree (I4′),
    /// normalized ([`normalize_bool`]).
    Tree(E6Term),
}

impl E6Expr {
    /// A short name for the node, for diagnostics.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            E6Expr::BoolCmp { op: BoolEqOp::Eq, .. } => "BoolCmp(==)",
            E6Expr::BoolCmp { op: BoolEqOp::Ne, .. } => "BoolCmp(!=)",
            E6Expr::Tree(term) if term.has_ite() => "DecisionTree",
            E6Expr::Tree(_) => "BoolTree",
        }
    }
}

fn is_value_neutral(stmt: &Statement) -> bool {
    // The SAME whitelist `admissible_body` skips (kept in step by the
    // `value_neutral_whitelists_agree` test below): anything not on it is
    // treated as effectful and fails the read closed.
    crate::admissible_body::is_value_neutral(stmt)
}

/// The bool leaf an operand denotes: a bare `bool` PARAMETER local, or a bare
/// single-assignment temporary holding one.
fn bool_leaf(
    func: &VerifiableFunction,
    op: &Operand,
    temps: &std::collections::BTreeMap<usize, BoolLeaf>,
) -> Option<BoolLeaf> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            if p.local >= 1 && p.local <= func.body.arg_count {
                (local_ty(func, p.local)? == &Ty::Bool).then_some(BoolLeaf::Param(p.local - 1))
            } else {
                temps.get(&p.local).copied()
            }
        }
        _ => None,
    }
}

/// Read `func` with the E6-ONLY reader, or `None` (fail closed).
///
/// Consulted by the E6 importer ONLY after `recognize_admissible_body` and
/// island forwarding both answered `None`. The composed Boolean Clean-origin
/// gate also reuses this unchanged reader through the canonical E6 importer
/// (module docs).
///
/// # What I1′ reads
///
/// ONE basic block that `Return`s, whose value statements are
///
/// * copies of `bool` parameters into fresh temporaries, each temporary
///   assigned exactly once and before it is read; then
/// * `_0 = Eq(l, r)` or `_0 = Ne(l, r)` — the LAST value statement — where
///   both operands are such parameters (directly or through a temporary),
///
/// in a function whose declared return type is `bool`. Everything else fails
/// closed: a projection anywhere, a write to a parameter, a temporary written
/// twice or read before it is written, a literal or non-`bool` operand, an
/// ordering (`Lt`/`Le`/`Gt`/`Ge`), any other rvalue or statement, a second
/// block.
///
/// FAITHFULNESS: `==`/`!=` on `bool` in MIR is exactly equality of the two
/// values (rustc lowers `bool` `PartialEq` to `BinOp::Eq`/`Ne`), and the leaf
/// rules make each operand the value the parameter carries, so
/// `decide (a = b)` / `!decide (a = b)` IS the returned value on every input.
/// The differential harness (`crates/trust-certify/tests/e6_differential.rs`)
/// executes both sides on all four input pairs at both opt levels.
///
/// # What I3′ reads, when the I1′ reading does not apply
///
/// A `bool` connective tree ([`read_e6_tree`]; the [`tree`] module docs give
/// the vocabulary and the faithfulness argument), returned as
/// [`E6Expr::Tree`].
#[must_use]
pub fn read_e6_body(func: &VerifiableFunction) -> Option<E6Expr> {
    read_e6_body_explained(func).ok()
}

/// [`read_e6_body`], with the TREE reader's refusal when neither reading
/// applies: the construct it stopped at, spelled for the refusal a user sees
/// (diagnostics read the `Err`; nothing that decides does).
///
/// The single-node I1′ reading comes FIRST and keeps its producer: a body it
/// reads is never offered to the tree reader, so every I1′ image and refusal
/// (including the single-domain `bool` mint's) is unchanged by I3′.
///
/// # Errors
///
/// The tree reader's refusal ([`read_e6_tree`]).
pub fn read_e6_body_explained(func: &VerifiableFunction) -> Result<E6Expr, String> {
    if let Some(node) = read_bool_cmp(func) {
        return Ok(node);
    }
    read_e6_tree(func).map(E6Expr::Tree)
}

/// The I1′ reading: one `==`/`!=` over two `bool` parameters.
fn read_bool_cmp(func: &VerifiableFunction) -> Option<E6Expr> {
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();
    if func.body.return_ty != Ty::Bool {
        return None;
    }
    let [block] = func.body.blocks.as_slice() else {
        return None;
    };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }
    let values: Vec<&Statement> = block.stmts.iter().filter(|s| !is_value_neutral(s)).collect();
    let (last, leading) = values.split_last()?;
    let mut temps: std::collections::BTreeMap<usize, BoolLeaf> = std::collections::BTreeMap::new();
    for stmt in leading {
        let Statement::Assign { place, rvalue: Rvalue::Use(op), .. } = stmt else {
            return None;
        };
        let local = place.local;
        if !place.projections.is_empty()
            || local == 0
            || local <= func.body.arg_count
            || local_ty(func, local)? != &Ty::Bool
            || temps.contains_key(&local)
        {
            return None;
        }
        let leaf = bool_leaf(func, op, &temps)?;
        temps.insert(local, leaf);
    }
    let Statement::Assign { place, rvalue: Rvalue::BinaryOp(binop, l, r), .. } = last else {
        return None;
    };
    if place.local != 0 || !place.projections.is_empty() {
        return None;
    }
    let op = match binop {
        BinOp::Eq => BoolEqOp::Eq,
        BinOp::Ne => BoolEqOp::Ne,
        _ => return None,
    };
    let left = bool_leaf(func, l, &temps)?;
    let right = bool_leaf(func, r, &temps)?;
    Some(E6Expr::BoolCmp { op, left, right })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{LocalDecl, Place, SourceSpan, VerifiableBody};

    fn func(locals: Vec<Ty>, arg_count: usize, blocks: Vec<BasicBlock>) -> VerifiableFunction {
        VerifiableFunction {
            name: "f".into(),
            def_path: "probe::f".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                return_ty: locals[0].clone(),
                locals: locals
                    .into_iter()
                    .enumerate()
                    .map(|(index, ty)| LocalDecl { index, ty, name: None })
                    .collect(),
                blocks,
                arg_count,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn asn(local: usize, rvalue: Rvalue) -> Statement {
        Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
    }

    fn cp(l: usize) -> Operand {
        Operand::Copy(Place::local(l))
    }

    fn ret(id: usize, stmts: Vec<Statement>) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator: Terminator::Return }
    }

    #[test]
    fn a_bit_operation_is_named_with_its_carrier() {
        let u = Ty::u64();
        let f = func(
            vec![u.clone(), u.clone(), u],
            2,
            vec![ret(0, vec![asn(0, Rvalue::BinaryOp(BinOp::BitAnd, cp(1), cp(2)))])],
        );
        assert_eq!(
            first_construct_outside_fragment(&f).as_deref(),
            Some("the bit operation `&` (`BinOp::BitAnd`) on `u64`")
        );
    }

    #[test]
    fn a_shift_outranks_its_amount_cast_and_its_assert() {
        // rustc's MIR for `v << 1` on u32 under overflow checks.
        let u32t = Ty::Int { width: 32, signed: false };
        let f = func(
            vec![u32t.clone(), u32t.clone(), u32t.clone(), Ty::Bool],
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        asn(2, Rvalue::Cast(Operand::Constant(ConstValue::Int(1)), u32t.clone())),
                        asn(
                            3,
                            Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Move(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(32, 32)),
                            ),
                        ),
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::local(3)),
                        expected: true,
                        msg: crate::AssertMessage::Overflow(BinOp::Shl),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: Default::default(),
                    },
                },
                ret(
                    1,
                    vec![asn(
                        0,
                        Rvalue::BinaryOp(BinOp::Shl, cp(1), Operand::Constant(ConstValue::Int(1))),
                    )],
                ),
            ],
        );
        assert_eq!(
            first_construct_outside_fragment(&f).as_deref(),
            Some("the shift `<<` (`BinOp::Shl`) on `u32` (and 2 further construct(s) outside it)")
        );
    }

    #[test]
    fn a_bool_ordering_and_a_cast_are_named() {
        let f = func(
            vec![Ty::Bool, Ty::Bool, Ty::Bool],
            2,
            vec![ret(0, vec![asn(0, Rvalue::BinaryOp(BinOp::Lt, cp(1), cp(2)))])],
        );
        assert_eq!(
            first_construct_outside_fragment(&f).as_deref(),
            Some("the ordering comparison `<` (`BinOp::Lt`) on `bool`")
        );
        let u8t = Ty::Int { width: 8, signed: false };
        let g = func(
            vec![Ty::u64(), u8t],
            1,
            vec![ret(0, vec![asn(0, Rvalue::Cast(cp(1), Ty::u64()))])],
        );
        assert_eq!(first_construct_outside_fragment(&g).as_deref(), Some("the cast `u8 as u64`"));
    }

    #[test]
    fn integer_comparisons_alone_are_a_composition_not_a_construct() {
        // `a < b || b < c || a == c`: every statement is a comparison leaf.
        let u = Ty::u64();
        let sw = |id: usize, discr: usize, f: usize, t: usize| BasicBlock {
            id: BlockId(id),
            stmts: vec![asn(discr, Rvalue::BinaryOp(BinOp::Lt, cp(1), cp(2)))],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(discr)),
                targets: vec![(0, BlockId(f))],
                otherwise: BlockId(t),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };
        let f = func(
            vec![Ty::Bool, u.clone(), u.clone(), u, Ty::Bool, Ty::Bool],
            3,
            vec![
                sw(0, 4, 1, 3),
                sw(1, 5, 2, 3),
                ret(2, vec![asn(0, Rvalue::BinaryOp(BinOp::Eq, cp(1), cp(3)))]),
                ret(3, vec![asn(0, Rvalue::Use(Operand::Constant(ConstValue::Bool(true))))]),
            ],
        );
        assert_eq!(first_construct_outside_fragment(&f), None);
        // Since I3′ the tree reader reads the composition itself.
        assert!(matches!(super::read_e6_body(&f), Some(super::E6Expr::Tree(_))));
    }

    #[test]
    fn a_loop_is_named_by_its_back_edge() {
        let u = Ty::u64();
        let f = func(
            vec![u.clone(), u],
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: cp(1),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                ret(2, vec![asn(0, Rvalue::Use(cp(1)))]),
            ],
        );
        assert_eq!(
            first_construct_outside_fragment(&f).as_deref(),
            Some("a loop (the back edge bb1 -> bb1)")
        );
    }

    // ---- read_e6_body (I1′) ------------------------------------------------

    fn bool2(stmts: Vec<Statement>, temps: usize) -> VerifiableFunction {
        let mut locals = vec![Ty::Bool, Ty::Bool, Ty::Bool];
        locals.extend(std::iter::repeat_n(Ty::Bool, temps));
        func(locals, 2, vec![ret(0, stmts)])
    }

    #[test]
    fn the_reader_reads_eq_and_ne_over_bool_parameters() {
        use super::{BoolEqOp, BoolLeaf, E6Expr, read_e6_body};
        let ne = bool2(vec![asn(0, Rvalue::BinaryOp(BinOp::Ne, cp(1), cp(2)))], 0);
        assert_eq!(
            read_e6_body(&ne),
            Some(E6Expr::BoolCmp {
                op: BoolEqOp::Ne,
                left: BoolLeaf::Param(0),
                right: BoolLeaf::Param(1)
            })
        );
        // Through single-assignment temporaries, as unoptimized MIR copies.
        let via_temps = bool2(
            vec![
                asn(3, Rvalue::Use(cp(1))),
                asn(4, Rvalue::Use(cp(2))),
                asn(
                    0,
                    Rvalue::BinaryOp(
                        BinOp::Ne,
                        Operand::Move(Place::local(3)),
                        Operand::Move(Place::local(4)),
                    ),
                ),
            ],
            2,
        );
        assert_eq!(
            read_e6_body(&via_temps),
            Some(E6Expr::BoolCmp {
                op: BoolEqOp::Ne,
                left: BoolLeaf::Param(0),
                right: BoolLeaf::Param(1)
            })
        );
    }

    /// The I1′ NODE's PINS (review H3): every shape below is outside the
    /// single `==`/`!=` reading, and several look like it. A red here is a
    /// soundness incident, not a test update. (The TREE reader reads some of
    /// them since I3′ — `the_i3_tree_reads_what_the_i1_node_refused` below
    /// says which, and why that is a reading and not a mistake.)
    #[test]
    fn the_i1_node_refuses_everything_else() {
        use super::read_bool_cmp;
        for (why, f) in i1_refusals() {
            assert_eq!(read_bool_cmp(&f), None, "the I1′ node read {why}");
        }
    }

    fn i1_refusals() -> Vec<(&'static str, VerifiableFunction)> {
        let one = |rv: Rvalue| bool2(vec![asn(0, rv)], 0);
        let u8t = Ty::Int { width: 8, signed: false };
        vec![
            ("an ordering <", one(Rvalue::BinaryOp(BinOp::Lt, cp(1), cp(2)))),
            ("an ordering <=", one(Rvalue::BinaryOp(BinOp::Le, cp(1), cp(2)))),
            ("an ordering >", one(Rvalue::BinaryOp(BinOp::Gt, cp(1), cp(2)))),
            ("a bool xor", one(Rvalue::BinaryOp(BinOp::BitXor, cp(1), cp(2)))),
            ("an unchecked op", one(Rvalue::UncheckedBinaryOp(BinOp::Eq, cp(1), cp(2)))),
            ("a checked op", one(Rvalue::CheckedBinaryOp(BinOp::Eq, cp(1), cp(2)))),
            ("a negation", one(Rvalue::UnaryOp(UnOp::Not, cp(1)))),
            (
                "a literal operand",
                one(Rvalue::BinaryOp(BinOp::Eq, Operand::Constant(ConstValue::Bool(false)), cp(2))),
            ),
            (
                "two literals",
                one(Rvalue::BinaryOp(
                    BinOp::Eq,
                    Operand::Constant(ConstValue::Bool(true)),
                    Operand::Constant(ConstValue::Bool(true)),
                )),
            ),
            (
                "a projected operand",
                one(Rvalue::BinaryOp(BinOp::Eq, Operand::Copy(Place::field(1, 0)), cp(2))),
            ),
            (
                "a temporary read before it is written",
                one(Rvalue::BinaryOp(BinOp::Eq, cp(3), cp(2))),
            ),
            (
                "a write to a parameter",
                bool2(
                    vec![
                        asn(1, Rvalue::Use(cp(2))),
                        asn(0, Rvalue::BinaryOp(BinOp::Eq, cp(1), cp(2))),
                    ],
                    0,
                ),
            ),
            (
                "a temporary written twice",
                bool2(
                    vec![
                        asn(3, Rvalue::Use(cp(1))),
                        asn(3, Rvalue::Use(cp(2))),
                        asn(0, Rvalue::BinaryOp(BinOp::Eq, cp(3), cp(2))),
                    ],
                    1,
                ),
            ),
            (
                "a comparison of a comparison",
                bool2(
                    vec![
                        asn(3, Rvalue::BinaryOp(BinOp::Eq, cp(1), cp(2))),
                        asn(0, Rvalue::BinaryOp(BinOp::Eq, cp(3), cp(2))),
                    ],
                    1,
                ),
            ),
            (
                "`!=` over u8",
                func(
                    vec![Ty::Bool, u8t.clone(), u8t],
                    2,
                    vec![ret(0, vec![asn(0, Rvalue::BinaryOp(BinOp::Ne, cp(1), cp(2)))])],
                ),
            ),
            (
                "a second block",
                func(
                    vec![Ty::Bool, Ty::Bool, Ty::Bool],
                    2,
                    vec![
                        BasicBlock {
                            id: BlockId(0),
                            stmts: vec![],
                            terminator: Terminator::Goto(BlockId(1)),
                        },
                        ret(1, vec![asn(0, Rvalue::BinaryOp(BinOp::Eq, cp(1), cp(2)))]),
                    ],
                ),
            ),
            (
                "a non-bool return",
                func(
                    vec![Ty::Int { width: 8, signed: false }, Ty::Bool, Ty::Bool],
                    2,
                    vec![ret(0, vec![asn(0, Rvalue::BinaryOp(BinOp::Eq, cp(1), cp(2)))])],
                ),
            ),
        ]
    }

    /// Since I3′ the TREE reader runs when the I1′ node answers `None`, and
    /// it READS some of the shapes above: each with the reading below, which
    /// is what the body computes on every input (the connectives and
    /// comparisons are total and pure; a temporary written twice holds the
    /// second value at the read; a `goto` is not a value). Two literals
    /// compared is a CONSTANT, the constant shape's scope, not read. The rest
    /// stay
    /// refused by every E6-only reading — the pins that matter for H1 (no
    /// ordering over `bool`) and H3 (no unchecked/checked op, no projection,
    /// no parameter write, no read before a write) among them.
    #[test]
    fn the_i3_tree_reads_what_the_i1_node_refused() {
        use super::{E6Carrier, E6Cmp, E6Term, read_e6_body};
        let p = E6Term::Param;
        let bcmp = |op, l, r| E6Term::Cmp {
            op,
            carrier: E6Carrier::Bool,
            left: Box::new(l),
            right: Box::new(r),
        };
        let reads: Vec<(&str, E6Term)> = vec![
            ("a bool xor", E6Term::Xor(Box::new(p(0)), Box::new(p(1)))),
            ("a negation", E6Term::Not(Box::new(p(0)))),
            ("a literal operand", bcmp(E6Cmp::Eq, E6Term::Bool(false), p(1))),
            ("a temporary written twice", bcmp(E6Cmp::Eq, p(1), p(1))),
            ("a comparison of a comparison", bcmp(E6Cmp::Eq, bcmp(E6Cmp::Eq, p(0), p(1)), p(1))),
            (
                "`!=` over u8",
                E6Term::Cmp {
                    op: E6Cmp::Ne,
                    carrier: E6Carrier::Unsigned(8),
                    left: Box::new(p(0)),
                    right: Box::new(p(1)),
                },
            ),
            ("a second block", bcmp(E6Cmp::Eq, p(0), p(1))),
        ];
        let reads: std::collections::BTreeMap<&str, E6Term> = reads.into_iter().collect();
        for (why, f) in i1_refusals() {
            match (reads.get(why), read_e6_body(&f)) {
                (Some(want), Some(E6Expr::Tree(got))) => assert_eq!(&got, want, "{why}"),
                (None, None) => {}
                (want, got) => panic!("{why}: expected the tree reading {want:?}, got {got:?}"),
            }
        }
    }

    #[test]
    fn value_neutral_whitelists_agree() {
        // The reader skips exactly what the recognizer skips.
        for stmt in [Statement::StorageLive(1), Statement::StorageDead(1), Statement::Nop] {
            assert!(super::is_value_neutral(&stmt));
        }
        assert!(!super::is_value_neutral(&asn(0, Rvalue::Use(cp(1)))));
    }
}
