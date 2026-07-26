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
pub(crate) mod contracts;
pub(crate) mod pred_vocab;
pub(crate) mod smtlib;
pub(crate) mod sort;
pub(crate) mod temporal;
#[cfg(test)]
mod tests;
pub(crate) mod vc;
pub(crate) mod vc_kind;

pub use borrow_encoding::*;
pub use contracts::*;
pub use pred_vocab::{
    CHECKER_CORE_PRED_VOCAB, CHECKER_CORE_SEMANTICS, CheckerCoreSemantics, PRED_VOCAB,
    checker_core_semantics, is_checker_core_pred, is_valid_pred, pred_arg_sorts,
};
pub use smtlib::escape_smtlib_symbol;
pub use sort::{RoundingMode, Sort, SortFromTy};
pub use temporal::*;
pub use vc::*;
pub use vc_kind::*;

use serde::{Deserialize, Serialize};

// The SMT formula AST lives in trust-ir-contract (cross-repo shared vocabulary).
// Re-exported so `trust_types::Formula` and `trust_types::formula::Formula` are
// unchanged. Its inherent methods (constructors, visitors, `to_smtlib`) ride
// along on the re-exported type.
pub use trust_ir_contract::Formula;

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
    let mut found = false;
    formula.visit(&mut |node| {
        found |= matches!(
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
        );
    });
    found
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
