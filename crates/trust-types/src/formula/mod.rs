// trust-types/formula: SMT-level formulas
//
// These are the verification conditions sent to solvers. Backend-agnostic —
// trust-router encodes these into ay/trust-wp/ty specific representations.
//
// The `Formula`/`Sort` SMT vocabulary and its SMT-LIB rendering now live in the
// `trust-ir-contract` leaf crate (shared across the Trust <-> backend boundary);
// they are re-exported here so `trust_types::Formula` / `trust_types::Sort` and
// the `formula::*` glob are unchanged. The VC/contract/temporal/predicate layers
// (which depend on the full MIR model) stay in this crate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod borrow_encoding;
mod contract_decline;
pub(crate) mod contracts;
pub(crate) mod pred_vocab;
pub(crate) mod refute_only;
mod remainder;
pub(crate) mod signed_bv_overflow;
pub(crate) mod smtlib;
pub(crate) mod sort;
pub(crate) mod temporal;
#[cfg(test)]
mod tests;
pub(crate) mod vc;
pub(crate) mod vc_kind;

pub use borrow_encoding::*;
pub use contract_decline::*;
pub use contracts::*;
pub use pred_vocab::{
    CHECKER_CORE_PRED_VOCAB, CHECKER_CORE_SEMANTICS, CheckerCoreSemantics, PRED_VOCAB,
    checker_core_semantics, is_checker_core_pred, is_valid_pred, pred_arg_sorts,
};
pub use refute_only::{RefuteOnlyOutcome, RefuteOnlyProvenance, RefuteOnlyVc};
pub use remainder::is_total_machine_remainder_divisor;
use serde::{Deserialize, Serialize};
pub use signed_bv_overflow::{
    SignedBvAddSubOverflow, asserted_signed_bv_addsub_overflows,
    signed_bv_addsub_overflow_sign_test, signed_bv_literal_value, signed_bv_operand_interval,
};
pub use smtlib::escape_smtlib_symbol;
pub use sort::{RoundingMode, Sort, SortFromTy, datatype_selector_name, sort_from_ty_with_defs};
pub use temporal::*;
// The SMT formula AST lives in trust-ir-contract (cross-repo shared vocabulary).
// Re-exported so `trust_types::Formula` and `trust_types::formula::Formula` are
// unchanged. Its inherent methods (constructors, visitors, `to_smtlib`) ride
// along on the re-exported type.
pub use trust_ir_contract::{Formula, RatLit};
pub use vc::*;
pub use vc_kind::*;

/// Visit every direct child of `formula` in [`Formula::children`] order without
/// allocating a temporary `Vec`, short-circuiting as soon as `f` returns `false`.
#[must_use]
pub fn all_formula_children<'a>(
    formula: &'a Formula,
    mut f: impl FnMut(&'a Formula) -> bool,
) -> bool {
    match formula {
        Formula::Bool(_)
        | Formula::Int(_)
        | Formula::UInt(_)
        | Formula::Rat(_)
        | Formula::BitVec { .. }
        | Formula::Var(..)
        | Formula::SymVar(..)
        | Formula::FpConst { .. }
        | Formula::FpNaN { .. }
        | Formula::FpInf { .. }
        | Formula::FpZero { .. }
        | Formula::FpRoundingMode(_) => true,

        Formula::Not(a)
        | Formula::Neg(a)
        | Formula::BvNot(a, _)
        | Formula::BvToInt(a, _, _)
        | Formula::IntToBv(a, _)
        | Formula::BvZeroExt(a, _)
        | Formula::BvSignExt(a, _)
        | Formula::BvExtract { inner: a, .. }
        | Formula::FpNeg(a)
        | Formula::FpAbs(a)
        | Formula::FpIsNaN(a)
        | Formula::FpIsInfinite(a)
        | Formula::FpIsZero(a)
        | Formula::FpIsNormal(a)
        | Formula::FpIsSubnormal(a)
        | Formula::FpIsNegative(a)
        | Formula::FpIsPositive(a)
        | Formula::FpFromBits { bits: a, .. }
        | Formula::FpToIeeeBv(a)
        | Formula::Forall(_, a)
        | Formula::Exists(_, a)
        | Formula::Sel { arg: a, .. }
        | Formula::IsCtor { arg: a, .. }
        | Formula::ConstArray { value: a, .. } => f(a),

        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b)
        | Formula::BvConcat(a, b)
        | Formula::Select(a, b)
        | Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvMul(a, b, _)
        | Formula::BvUDiv(a, b, _)
        | Formula::BvSDiv(a, b, _)
        | Formula::BvURem(a, b, _)
        | Formula::BvSRem(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::BvShl(a, b, _)
        | Formula::BvLShr(a, b, _)
        | Formula::BvAShr(a, b, _)
        | Formula::BvULt(a, b, _)
        | Formula::BvULe(a, b, _)
        | Formula::BvSLt(a, b, _)
        | Formula::BvSLe(a, b, _)
        | Formula::FpToSbv { rm: a, value: b, .. }
        | Formula::FpToUbv { rm: a, value: b, .. }
        | Formula::FpFromSbv { rm: a, value: b, .. }
        | Formula::FpFromUbv { rm: a, value: b, .. }
        | Formula::FpConvert { rm: a, value: b, .. }
        | Formula::FpRem(a, b)
        | Formula::FpMin(a, b)
        | Formula::FpMax(a, b)
        | Formula::FpEq(a, b)
        | Formula::FpLt(a, b)
        | Formula::FpLe(a, b)
        | Formula::FpGt(a, b)
        | Formula::FpGe(a, b)
        | Formula::FpSqrt(a, b) => f(a) && f(b),

        Formula::Ite(a, b, c)
        | Formula::Store(a, b, c)
        | Formula::FpAdd(a, b, c)
        | Formula::FpSub(a, b, c)
        | Formula::FpMul(a, b, c)
        | Formula::FpDiv(a, b, c) => f(a) && f(b) && f(c),

        Formula::FpFma(a, b, c, d) => f(a) && f(b) && f(c) && f(d),

        Formula::And(terms)
        | Formula::Or(terms)
        | Formula::Pred(_, terms)
        | Formula::Ctor { args: terms, .. }
        | Formula::FnApp { args: terms, .. } => terms.iter().all(&mut f),

        other => other.children().into_iter().all(&mut f),
    }
}

/// Visit every direct child of `formula` in [`Formula::children`] order without
/// allocating a temporary `Vec`.
pub fn for_each_formula_child<'a>(formula: &'a Formula, mut f: impl FnMut(&'a Formula)) {
    let _ = all_formula_children(formula, |child| {
        f(child);
        true
    });
}

/// Pairwise predicate over the direct children of `lhs` and `rhs` in
/// [`Formula::children`] order without allocating temporary child `Vec`s.
/// Returns `false` if `lhs` and `rhs` have different child counts or if `f`
/// returns `false` for any child pair.
#[must_use]
pub fn all_formula_children_zip<'a, 'b>(
    lhs: &'a Formula,
    rhs: &'b Formula,
    mut f: impl FnMut(&'a Formula, &'b Formula) -> bool,
) -> bool {
    match (lhs, rhs) {
        (
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::Rat(_)
            | Formula::BitVec { .. }
            | Formula::Var(..)
            | Formula::SymVar(..)
            | Formula::FpConst { .. }
            | Formula::FpNaN { .. }
            | Formula::FpInf { .. }
            | Formula::FpZero { .. }
            | Formula::FpRoundingMode(_),
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::Rat(_)
            | Formula::BitVec { .. }
            | Formula::Var(..)
            | Formula::SymVar(..)
            | Formula::FpConst { .. }
            | Formula::FpNaN { .. }
            | Formula::FpInf { .. }
            | Formula::FpZero { .. }
            | Formula::FpRoundingMode(_),
        ) => true,

        (
            Formula::Not(a)
            | Formula::Neg(a)
            | Formula::BvNot(a, _)
            | Formula::BvToInt(a, _, _)
            | Formula::IntToBv(a, _)
            | Formula::BvZeroExt(a, _)
            | Formula::BvSignExt(a, _)
            | Formula::BvExtract { inner: a, .. }
            | Formula::FpNeg(a)
            | Formula::FpAbs(a)
            | Formula::FpIsNaN(a)
            | Formula::FpIsInfinite(a)
            | Formula::FpIsZero(a)
            | Formula::FpIsNormal(a)
            | Formula::FpIsSubnormal(a)
            | Formula::FpIsNegative(a)
            | Formula::FpIsPositive(a)
            | Formula::FpFromBits { bits: a, .. }
            | Formula::FpToIeeeBv(a)
            | Formula::Forall(_, a)
            | Formula::Exists(_, a)
            | Formula::Sel { arg: a, .. }
            | Formula::IsCtor { arg: a, .. }
            | Formula::ConstArray { value: a, .. },
            Formula::Not(b)
            | Formula::Neg(b)
            | Formula::BvNot(b, _)
            | Formula::BvToInt(b, _, _)
            | Formula::IntToBv(b, _)
            | Formula::BvZeroExt(b, _)
            | Formula::BvSignExt(b, _)
            | Formula::BvExtract { inner: b, .. }
            | Formula::FpNeg(b)
            | Formula::FpAbs(b)
            | Formula::FpIsNaN(b)
            | Formula::FpIsInfinite(b)
            | Formula::FpIsZero(b)
            | Formula::FpIsNormal(b)
            | Formula::FpIsSubnormal(b)
            | Formula::FpIsNegative(b)
            | Formula::FpIsPositive(b)
            | Formula::FpFromBits { bits: b, .. }
            | Formula::FpToIeeeBv(b)
            | Formula::Forall(_, b)
            | Formula::Exists(_, b)
            | Formula::Sel { arg: b, .. }
            | Formula::IsCtor { arg: b, .. }
            | Formula::ConstArray { value: b, .. },
        ) => f(a, b),

        (
            Formula::Implies(a1, a2)
            | Formula::Eq(a1, a2)
            | Formula::Lt(a1, a2)
            | Formula::Le(a1, a2)
            | Formula::Gt(a1, a2)
            | Formula::Ge(a1, a2)
            | Formula::Add(a1, a2)
            | Formula::Sub(a1, a2)
            | Formula::Mul(a1, a2)
            | Formula::Div(a1, a2)
            | Formula::Rem(a1, a2)
            | Formula::BvConcat(a1, a2)
            | Formula::Select(a1, a2)
            | Formula::BvAdd(a1, a2, _)
            | Formula::BvSub(a1, a2, _)
            | Formula::BvMul(a1, a2, _)
            | Formula::BvUDiv(a1, a2, _)
            | Formula::BvSDiv(a1, a2, _)
            | Formula::BvURem(a1, a2, _)
            | Formula::BvSRem(a1, a2, _)
            | Formula::BvAnd(a1, a2, _)
            | Formula::BvOr(a1, a2, _)
            | Formula::BvXor(a1, a2, _)
            | Formula::BvShl(a1, a2, _)
            | Formula::BvLShr(a1, a2, _)
            | Formula::BvAShr(a1, a2, _)
            | Formula::BvULt(a1, a2, _)
            | Formula::BvULe(a1, a2, _)
            | Formula::BvSLt(a1, a2, _)
            | Formula::BvSLe(a1, a2, _)
            | Formula::FpToSbv { rm: a1, value: a2, .. }
            | Formula::FpToUbv { rm: a1, value: a2, .. }
            | Formula::FpFromSbv { rm: a1, value: a2, .. }
            | Formula::FpFromUbv { rm: a1, value: a2, .. }
            | Formula::FpConvert { rm: a1, value: a2, .. }
            | Formula::FpRem(a1, a2)
            | Formula::FpMin(a1, a2)
            | Formula::FpMax(a1, a2)
            | Formula::FpEq(a1, a2)
            | Formula::FpLt(a1, a2)
            | Formula::FpLe(a1, a2)
            | Formula::FpGt(a1, a2)
            | Formula::FpGe(a1, a2)
            | Formula::FpSqrt(a1, a2),
            Formula::Implies(b1, b2)
            | Formula::Eq(b1, b2)
            | Formula::Lt(b1, b2)
            | Formula::Le(b1, b2)
            | Formula::Gt(b1, b2)
            | Formula::Ge(b1, b2)
            | Formula::Add(b1, b2)
            | Formula::Sub(b1, b2)
            | Formula::Mul(b1, b2)
            | Formula::Div(b1, b2)
            | Formula::Rem(b1, b2)
            | Formula::BvConcat(b1, b2)
            | Formula::Select(b1, b2)
            | Formula::BvAdd(b1, b2, _)
            | Formula::BvSub(b1, b2, _)
            | Formula::BvMul(b1, b2, _)
            | Formula::BvUDiv(b1, b2, _)
            | Formula::BvSDiv(b1, b2, _)
            | Formula::BvURem(b1, b2, _)
            | Formula::BvSRem(b1, b2, _)
            | Formula::BvAnd(b1, b2, _)
            | Formula::BvOr(b1, b2, _)
            | Formula::BvXor(b1, b2, _)
            | Formula::BvShl(b1, b2, _)
            | Formula::BvLShr(b1, b2, _)
            | Formula::BvAShr(b1, b2, _)
            | Formula::BvULt(b1, b2, _)
            | Formula::BvULe(b1, b2, _)
            | Formula::BvSLt(b1, b2, _)
            | Formula::BvSLe(b1, b2, _)
            | Formula::FpToSbv { rm: b1, value: b2, .. }
            | Formula::FpToUbv { rm: b1, value: b2, .. }
            | Formula::FpFromSbv { rm: b1, value: b2, .. }
            | Formula::FpFromUbv { rm: b1, value: b2, .. }
            | Formula::FpConvert { rm: b1, value: b2, .. }
            | Formula::FpRem(b1, b2)
            | Formula::FpMin(b1, b2)
            | Formula::FpMax(b1, b2)
            | Formula::FpEq(b1, b2)
            | Formula::FpLt(b1, b2)
            | Formula::FpLe(b1, b2)
            | Formula::FpGt(b1, b2)
            | Formula::FpGe(b1, b2)
            | Formula::FpSqrt(b1, b2),
        ) => f(a1, b1) && f(a2, b2),

        (
            Formula::Ite(a1, a2, a3)
            | Formula::Store(a1, a2, a3)
            | Formula::FpAdd(a1, a2, a3)
            | Formula::FpSub(a1, a2, a3)
            | Formula::FpMul(a1, a2, a3)
            | Formula::FpDiv(a1, a2, a3),
            Formula::Ite(b1, b2, b3)
            | Formula::Store(b1, b2, b3)
            | Formula::FpAdd(b1, b2, b3)
            | Formula::FpSub(b1, b2, b3)
            | Formula::FpMul(b1, b2, b3)
            | Formula::FpDiv(b1, b2, b3),
        ) => f(a1, b1) && f(a2, b2) && f(a3, b3),

        (Formula::FpFma(a1, a2, a3, a4), Formula::FpFma(b1, b2, b3, b4)) => {
            f(a1, b1) && f(a2, b2) && f(a3, b3) && f(a4, b4)
        }

        (
            Formula::And(ta)
            | Formula::Or(ta)
            | Formula::Pred(_, ta)
            | Formula::Ctor { args: ta, .. }
            | Formula::FnApp { args: ta, .. },
            Formula::And(tb)
            | Formula::Or(tb)
            | Formula::Pred(_, tb)
            | Formula::Ctor { args: tb, .. }
            | Formula::FnApp { args: tb, .. },
        ) => ta.len() == tb.len() && ta.iter().zip(tb.iter()).all(|(a, b)| f(a, b)),

        (other_a, other_b) => {
            let ca = other_a.children();
            let cb = other_b.children();
            ca.len() == cb.len() && ca.into_iter().zip(cb).all(|(a, b)| f(a, b))
        }
    }
}

/// Pre-order depth-first predicate over `formula` without allocating per-node
/// child `Vec`s, short-circuiting as soon as `f` returns `false`.
#[must_use]
pub fn all_formula_nodes<'a>(
    formula: &'a Formula,
    f: &mut impl FnMut(&'a Formula) -> bool,
) -> bool {
    f(formula) && all_formula_children(formula, |child| all_formula_nodes(child, f))
}

/// Pre-order depth-first existential predicate over `formula` without allocating
/// per-node child `Vec`s, short-circuiting as soon as `f` returns `true`.
#[must_use]
pub fn any_formula_node<'a>(
    formula: &'a Formula,
    f: &mut impl FnMut(&'a Formula) -> bool,
) -> bool {
    !all_formula_nodes(formula, &mut |node| !f(node))
}

/// Pre-order depth-first visit of `formula` without allocating per-node child `Vec`s.
pub fn visit_formula_nodes<'a>(formula: &'a Formula, f: &mut impl FnMut(&'a Formula)) {
    let _ = all_formula_nodes(formula, &mut |node| {
        f(node);
        true
    });
}

/// Visit every free variable name (`Var` and `SymVar`, excluding quantifier-bound
/// names) in `formula` without allocating per-node child `Vec`s or cloning `String`s,
/// short-circuiting as soon as `f` returns `false`.
#[must_use]
pub fn all_free_variable_names<'a>(
    formula: &'a Formula,
    f: &mut impl FnMut(&'a str) -> bool,
) -> bool {
    fn walk<'a>(
        formula: &'a Formula,
        bound: &mut Vec<&'a trust_ir_contract::Symbol>,
        f: &mut impl FnMut(&'a str) -> bool,
    ) -> bool {
        match formula {
            Formula::Var(name, _) => {
                if bound.iter().any(|sym| sym.as_str() == name.as_str()) {
                    true
                } else {
                    f(name.as_str())
                }
            }
            Formula::SymVar(sym, _) => {
                if bound.contains(&sym) || bound.iter().any(|b| b.as_str() == sym.as_str()) {
                    true
                } else {
                    f(sym.as_str())
                }
            }
            Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
                let prev_len = bound.len();
                bound.extend(bindings.iter().map(|(sym, _)| sym));
                let ok = walk(body, bound, f);
                bound.truncate(prev_len);
                ok
            }
            other => all_formula_children(other, |child| walk(child, bound, f)),
        }
    }
    let mut bound = Vec::new();
    walk(formula, &mut bound, f)
}

/// Existential counterpart to [`all_free_variable_names`]: true when at least one
/// free variable name in `formula` satisfies `f`, without allocating a `FxHashSet<String>`
/// or per-node child `Vec`s.
#[must_use]
pub fn any_free_variable_name<'a>(
    formula: &'a Formula,
    f: &mut impl FnMut(&'a str) -> bool,
) -> bool {
    !all_free_variable_names(formula, &mut |name| !f(name))
}

/// Visit every free variable name occurrence in `formula` without allocating
/// per-node child `Vec`s or cloning `String`s.
pub fn for_each_free_variable_name<'a>(formula: &'a Formula, f: &mut impl FnMut(&'a str)) {
    let _ = all_free_variable_names(formula, &mut |name| {
        f(name);
        true
    });
}

/// Whether a formula carries any bitvector-theory structure — a `Bv*` node, a
/// `BitVec` literal, an `Int`↔BV conversion, or a `BitVec`-sorted variable.
///
/// The Machine{w} contract lane (ratified L1 rule 4) emits postcondition VCs
/// whose arithmetic deliberately WRAPS at its declared width. Every
/// mathematical-integer device — interval abstract interpretation, the widened
/// non-wrapping BV re-encoders, `Int`-domain fact augmentation — misreads that
/// semantics (the `result + 1 > result` false-proof vector is exactly the
/// unbounded reading of a wrapping clause), so such passes consult this
/// predicate and leave bitvector-bearing formulas untouched.
#[must_use]
pub fn formula_mentions_bitvector_theory(formula: &Formula) -> bool {
    any_formula_node(formula, &mut |node| {
        matches!(
            node,
            Formula::BitVec { .. }
                | Formula::BvAdd(..)
                | Formula::BvSub(..)
                | Formula::BvMul(..)
                | Formula::BvUDiv(..)
                | Formula::BvSDiv(..)
                | Formula::BvURem(..)
                | Formula::BvSRem(..)
                | Formula::BvAnd(..)
                | Formula::BvOr(..)
                | Formula::BvXor(..)
                | Formula::BvNot(..)
                | Formula::BvShl(..)
                | Formula::BvLShr(..)
                | Formula::BvAShr(..)
                | Formula::BvULt(..)
                | Formula::BvULe(..)
                | Formula::BvSLt(..)
                | Formula::BvSLe(..)
                | Formula::BvToInt(..)
                | Formula::IntToBv(..)
                | Formula::BvExtract { .. }
                | Formula::BvConcat(..)
                | Formula::BvZeroExt(..)
                | Formula::BvSignExt(..)
        ) || matches!(
            node,
            Formula::Var(_, Sort::BitVec(_)) | Formula::SymVar(_, Sort::BitVec(_))
        )
    })
}

/// Proof level tier, used by the router to select appropriate backends.
///
/// # Examples
///
/// ```
/// use trust_types::ProofLevel;
///
/// // Proof levels are ordered: L0 < L1 < L2
/// assert!(ProofLevel::L0Safety < ProofLevel::L1Functional);
/// assert!(ProofLevel::L1Functional < ProofLevel::L2Domain);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofLevel {
    /// L0: Safety — no panics, no UB (overflow, bounds, div-by-zero).
    L0Safety,
    /// L1: Functional — postconditions hold, contracts satisfied.
    L1Functional,
    /// L2: Domain — temporal properties, distributed protocol correctness.
    L2Domain,
}
